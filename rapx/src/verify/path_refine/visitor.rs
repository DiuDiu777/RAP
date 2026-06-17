//! Backward path visitor — walks a finite path backward from a callsite and
//! keeps only MIR items that can affect the required property.
//!
//! The def-use layer lives in [`super::super::def_use`]; this module focuses on
//! the path-level control flow decisions: calls, SCC exits, and path-condition
//! branches.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::Body;
use rustc_middle::mir::{BasicBlock, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use crate::analysis::dataflow::graph::build_dataflow_graph;
use crate::graphs::dataflow::DataflowGraph;

use super::super::{
    contract,
    def_use::{RelevantPlaces, bind_callsite_roots, operand_uses, terminator_use_def},
    helpers::{Callsite, CallsiteLocation},
    path::{Path, PathStep},
};

use crate::analysis::path_analysis::{PathNode, PathTree};

use super::{
    call_visit,
    types::{BackwardItem, ForgetReason, KeepReason, RelevantMirItems},
};

/// Entry point for backward path visiting.
pub struct BackwardVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> BackwardVisitor<'tcx> {
    /// Create a backward visitor over the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Return the compiler type context owned by this visitor.
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Build the initial relevant-MIR item set for a path and property.
    pub fn start_visit(
        &self,
        callsite: CallsiteLocation,
        path: &Path,
        property: &contract::Property<'tcx>,
    ) -> RelevantMirItems<'tcx> {
        RelevantMirItems {
            callsite,
            property: property.clone(),
            path: path.clone(),
            items: Vec::new(),
            roots: RelevantPlaces::from_property(property),
        }
    }

    /// Visit one `(callsite, path, property)` item backward.
    pub fn visit(
        &self,
        callsite: &Callsite<'tcx>,
        path: &Path,
        property: &contract::Property<'tcx>,
    ) -> RelevantMirItems<'tcx> {
        let mut visit = self.start_visit(callsite.location(), path, property);
        bind_callsite_roots(self.tcx, &mut visit.roots, callsite);
        self.visit_path(callsite.caller, &callsite.location(), path, &mut visit);
        visit
    }

    /// Visit one `(checkpoint, path, property)` item backward for struct
    /// invariant checks.
    ///
    /// Unlike [`visit`], this does not bind callee parameter roots because the
    /// property places are already resolved in the caller's local namespace
    /// (e.g., struct field accesses on `self`).
    pub fn visit_for_checkpoint(
        &self,
        caller: DefId,
        checkpoint: CallsiteLocation,
        path: &Path,
        property: &contract::Property<'tcx>,
    ) -> RelevantMirItems<'tcx> {
        let mut visit = self.start_visit(checkpoint, path, property);
        self.visit_path(caller, &checkpoint, path, &mut visit);
        visit
    }

    /// Visit a path tree in post-order, sharing backward analysis across
    /// common prefixes. Merges child-relevance sets at branch nodes (the
    /// union is a sound over-approximation). Returns per-leaf results.
    ///
    /// Callee parameter roots are bound at callsite nodes.
    pub fn visit_path_tree(
        &self,
        tree: &PathTree,
        target_block: usize,
        callsite: &Callsite<'tcx>,
        property: &contract::Property<'tcx>,
    ) -> Vec<RelevantMirItems<'tcx>> {
        self.visit_path_tree_impl(
            tree, target_block, callsite.caller, callsite.block,
            Some(callsite), property,
        )
    }

    /// Like [`visit_path_tree`] but without callee-root binding (used for
    /// struct-invariant checks where property places are already in the
    /// caller's local namespace).
    pub fn visit_path_tree_for_checkpoint(
        &self,
        tree: &PathTree,
        target_block: usize,
        caller: rustc_hir::def_id::DefId,
        callsite_loc: CallsiteLocation,
        property: &contract::Property<'tcx>,
    ) -> Vec<RelevantMirItems<'tcx>> {
        self.visit_path_tree_impl(tree, target_block, caller, callsite_loc.block, None, property)
    }

    /// Internal implementation shared by both public tree-visit methods.
    fn visit_path_tree_impl(
        &self,
        tree: &PathTree,
        target_block: usize,
        caller: rustc_hir::def_id::DefId,
        callsite_block: BasicBlock,
        bind_callsite: Option<&Callsite<'tcx>>,
        property: &contract::Property<'tcx>,
    ) -> Vec<RelevantMirItems<'tcx>> {
        let Some(root) = tree.root() else {
            return Vec::new();
        };
        let callsite_loc = CallsiteLocation {
            caller,
            block: callsite_block,
        };
        let body = self.tcx.optimized_mir(caller);
        let flow = build_dataflow_graph(self.tcx, caller);
        let keep_alloc = matches!(
            property.kind,
            contract::PropertyKind::Allocated | contract::PropertyKind::ValidPtr
        );

        // Pass 1: post-order — compute items per node (merged).
        let mut node_items: std::collections::HashMap<
            usize,
            Vec<BackwardItem<'tcx>>,
        > = std::collections::HashMap::new();
        let mut leaf_nodes: Vec<usize> = Vec::new();

        Self::build_node_items(
            self,
            root,
            target_block,
            callsite_loc.block,
            bind_callsite,
            property,
            &body,
            &flow,
            keep_alloc,
            &mut node_items,
            &mut leaf_nodes,
        );

        // Pass 2: pre-order — collect per-path items and build results.
        let mut results = Vec::new();
        let mut prefix = Vec::new();
        let mut accumulated_items: Vec<BackwardItem<'tcx>> = Vec::new();

        Self::collect_path_results(
            self,
            root,
            target_block,
            &callsite_loc,
            property,
            &mut prefix,
            &mut accumulated_items,
            &node_items,
            &mut results,
        );

        results
    }

    /// Post-order: compute items for each node and record callsite leaves.
    fn build_node_items(
        visitor: &Self,
        node: &PathNode,
        target_block: usize,
        callsite_block: BasicBlock,
        bind_callsite: Option<&Callsite<'tcx>>,
        property: &contract::Property<'tcx>,
        body: &'tcx rustc_middle::mir::Body<'tcx>,
        flow: &DataflowGraph,
        keep_alloc: bool,
        node_items: &mut std::collections::HashMap<usize, Vec<BackwardItem<'tcx>>>,
        leaf_nodes: &mut Vec<usize>,
    ) -> RelevantPlaces {
        let node_key = node as *const PathNode as usize;

        if node.block == target_block {
            let mut relevant = RelevantPlaces::from_property(property);
            if let Some(cs) = bind_callsite {
                bind_callsite_roots(visitor.tcx, &mut relevant, cs);
            }
            let mut items = Vec::new();
            // callsite terminator
            items.push(BackwardItem::Terminator {
                block: callsite_block,
                kind: KeepReason::Callsite,
            });
            // statements in reverse
            let block_data = &body.basic_blocks[callsite_block];
            for (si, stmt) in block_data.statements.iter().enumerate().rev() {
                visitor.visit_statement(
                    callsite_block, si, stmt, flow,
                    &mut relevant, &mut items, keep_alloc,
                );
            }
            node_items.insert(node_key, items);
            leaf_nodes.push(node_key);
            return relevant;
        }

        let mut merged_relevant = RelevantPlaces::new();
        let mut items = Vec::new();

        for child in &node.children {
            let child_relevant = Self::build_node_items(
                visitor, child, target_block, callsite_block,
                bind_callsite, property, body, flow, keep_alloc,
                node_items, leaf_nodes,
            );
            merged_relevant.extend(child_relevant);
        }

        let block = BasicBlock::from(node.block);
        let block_data = &body.basic_blocks[block];
        visitor.visit_terminator(
            block, block_data.terminator(), flow, body,
            &mut merged_relevant, &mut items, keep_alloc,
        );
        for (si, stmt) in block_data.statements.iter().enumerate().rev() {
            visitor.visit_statement(
                block, si, stmt, flow,
                &mut merged_relevant, &mut items, keep_alloc,
            );
        }

        node_items.insert(node_key, items);
        merged_relevant
    }

    /// Pre-order: walk from root toward callsite leaves, accumulating items
    /// along the path. At each callsite leaf, emit a `RelevantMirItems`.
    fn collect_path_results(
        visitor: &Self,
        node: &PathNode,
        target_block: usize,
        callsite_loc: &super::super::helpers::CallsiteLocation,
        property: &contract::Property<'tcx>,
        prefix: &mut Vec<usize>,
        accumulated_items: &mut Vec<BackwardItem<'tcx>>,
        node_items: &std::collections::HashMap<usize, Vec<BackwardItem<'tcx>>>,
        results: &mut Vec<RelevantMirItems<'tcx>>,
    ) {
        let node_key = node as *const PathNode as usize;

        // Push this node's items (collected backward: terminator then
        // last→first statements). Accumulate in backward order; reversed
        // at callsite leaves to produce forward order.
        if let Some(items) = node_items.get(&node_key) {
            accumulated_items.extend(items.iter().cloned());
        }

        prefix.push(node.block);
        if node.block == target_block {
            let mut items = accumulated_items.clone();
            items.reverse(); // backward → forward order
            let steps: Vec<PathStep> = prefix
                .iter()
                .map(|&b| PathStep::Block(BasicBlock::from(b)))
                .chain(std::iter::once(PathStep::Callsite(*callsite_loc)))
                .collect();
            let path = Path {
                target: *callsite_loc,
                start: super::super::path::PathStart::FunctionEntry,
                steps,
            };
            let visit = RelevantMirItems {
                callsite: *callsite_loc,
                property: property.clone(),
                path,
                items,
                roots: RelevantPlaces::from_property(property),
            };
            results.push(visit);
        } else {
            for child in &node.children {
                Self::collect_path_results(
                    visitor, child, target_block, callsite_loc, property,
                    prefix, accumulated_items, node_items, results,
                );
            }
        }

        // Pop this node's items
        if let Some(items) = node_items.get(&node_key) {
            accumulated_items.truncate(accumulated_items.len() - items.len());
        }
        prefix.pop();
    }

    fn visit_path(
        &self,
        caller: DefId,
        callsite_loc: &CallsiteLocation,
        path: &Path,
        visit: &mut RelevantMirItems<'tcx>,
    ) {
        let mut relevant = visit.roots.clone();
        let mut items: Vec<BackwardItem<'tcx>> = Vec::new();
        let body = self.tcx.optimized_mir(caller);
        let flow = build_dataflow_graph(self.tcx, caller);

        let keep_allocation_invalidations = matches!(
            visit.property.kind,
            contract::PropertyKind::Allocated | contract::PropertyKind::ValidPtr
        );

        for step in path.steps.iter().rev() {
            self.visit_path_step_inner(
                step,
            &callsite_loc,
                &body,
                &flow,
                &mut relevant,
                &mut items,
                keep_allocation_invalidations,
            );
        }

        items.reverse();
        visit.items = items;
    }

    fn visit_path_step_inner(
        &self,
        step: &PathStep,
        callsite_loc: &CallsiteLocation,
        body: &'tcx Body<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
        keep_allocation_invalidations: bool,
    ) {
        match step {
            PathStep::Callsite(location) => {
                if *location != *callsite_loc {
                    return;
                }
                items.push(BackwardItem::Terminator {
                    block: location.block,
                    kind: KeepReason::Callsite,
                });
            }
            PathStep::Block(block) => {
                let block_data = &body.basic_blocks[*block];
                if *block != callsite_loc.block {
                    self.visit_terminator(
                        *block,
                        block_data.terminator(),
                        flow,
                        body,
                        relevant,
                        items,
                        keep_allocation_invalidations,
                    );
                }
                for (statement_index, statement) in block_data.statements.iter().enumerate().rev() {
                    self.visit_statement(
                        *block,
                        statement_index,
                        statement,
                        flow,
                        relevant,
                        items,
                        keep_allocation_invalidations,
                    );
                }
            }
        }
    }

    /// Visit one MIR statement against the current relevance frontier.
    fn visit_statement(
        &self,
        block: BasicBlock,
        statement_index: usize,
        statement: &'tcx rustc_middle::mir::Statement<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
        keep_allocation_invalidations: bool,
    ) {
        if keep_allocation_invalidations && matches!(statement.kind, StatementKind::StorageDead(_))
        {
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: KeepReason::Invalidation,
            });
            return;
        }

        let mut defs = RelevantPlaces::new();
        match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, _) = &**assign;
                defs.insert_mir_place(place);
            }
            StatementKind::StorageDead(local) => {
                defs.insert_local(*local);
            }
            _ => {}
        }

        if defs.intersects(relevant) {
            let uses = collect_statement_uses(statement, block, statement_index, flow);
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: statement_keep_reason(statement),
            });
            relevant.remove_all(&defs);
            relevant.extend(uses);
            return;
        }

        if statement_invalidates_relevant(statement, relevant) {
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: KeepReason::Invalidation,
            });
        } else if statement_can_refine(statement) {
            let mut uses = RelevantPlaces::new();
            for &local in &defs.locals {
                for &edge_idx in &flow.node(local).in_edges {
                    let edge = &flow.edges[edge_idx];
                    if edge.block == block.as_usize() && edge.statement_index == statement_index {
                        uses.insert_local(edge.src);
                    }
                }
            }
            if uses.intersects(relevant) {
                items.push(BackwardItem::Statement {
                    block,
                    statement_index,
                    kind: KeepReason::RuntimeCheck,
                });
            }
        }
    }

    /// Visit one MIR terminator against the current relevance frontier.
    fn visit_terminator(
        &self,
        block: BasicBlock,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        flow: &DataflowGraph,
        body: &Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
        keep_allocation_invalidations: bool,
    ) {
        if keep_allocation_invalidations && matches!(terminator.kind, TerminatorKind::Drop { .. }) {
            items.push(BackwardItem::Terminator {
                block,
                kind: KeepReason::Invalidation,
            });
            return;
        }

        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            call_visit::visit(
                self.tcx,
                block,
                func,
                args,
                destination,
                flow,
                body,
                relevant,
                items,
            );
            return;
        }

        let use_def = terminator_use_def(terminator);
        if terminator_is_path_condition(terminator) {
            items.push(BackwardItem::Terminator {
                block,
                kind: KeepReason::PathCondition,
            });
            relevant.extend(use_def.uses.clone());
            return;
        }

        if use_def.defs.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: terminator_definition_reason(terminator),
            });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if use_def.uses.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: terminator_use_reason(terminator),
            });
        }
    }
}

// ── classification helpers ──────────────────────────────────────────────

fn statement_keep_reason(statement: &rustc_middle::mir::Statement<'_>) -> KeepReason {
    match &statement.kind {
        StatementKind::Assign(assign) => {
            let (_, rvalue) = &**assign;
            match rvalue {
                rustc_middle::mir::Rvalue::Ref(_, _, _)
                | rustc_middle::mir::Rvalue::RawPtr(_, _)
                | rustc_middle::mir::Rvalue::Cast(_, _, _)
                | rustc_middle::mir::Rvalue::CopyForDeref(_)
                | rustc_middle::mir::Rvalue::BinaryOp(_, _) => KeepReason::PointerFlow,
                _ => KeepReason::Definition,
            }
        },
        StatementKind::StorageDead(_) => KeepReason::Invalidation,
        _ => KeepReason::Definition,
    }
}

fn statement_can_refine(statement: &rustc_middle::mir::Statement<'_>) -> bool {
    matches!(&statement.kind, StatementKind::Assign(assign) if matches!(
        &**assign,
        (
            _,
            rustc_middle::mir::Rvalue::BinaryOp(_, _)
            | rustc_middle::mir::Rvalue::UnaryOp(_, _)
            | rustc_middle::mir::Rvalue::Cast(_, _, _),
        )
    ))
}

fn statement_invalidates_relevant(
    statement: &rustc_middle::mir::Statement<'_>,
    relevant: &RelevantPlaces,
) -> bool {
    match &statement.kind {
        StatementKind::StorageDead(local) => relevant.locals.contains(local),
        _ => false,
    }
}

fn terminator_is_path_condition(terminator: &rustc_middle::mir::Terminator<'_>) -> bool {
    matches!(
        terminator.kind,
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. }
    )
}

fn terminator_definition_reason(terminator: &rustc_middle::mir::Terminator<'_>) -> KeepReason {
    match terminator.kind {
        TerminatorKind::Call { .. } => KeepReason::UnknownEffect,
        _ => KeepReason::Definition,
    }
}

fn terminator_use_reason(terminator: &rustc_middle::mir::Terminator<'_>) -> KeepReason {
    match terminator.kind {
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. } => {
            KeepReason::PathCondition
        }
        TerminatorKind::Drop { .. } => KeepReason::Invalidation,
        TerminatorKind::Call { .. } => KeepReason::UnknownEffect,
        _ => KeepReason::UnknownEffect,
    }
}

fn terminator_may_havoc(terminator: &rustc_middle::mir::Terminator<'_>) -> bool {
    matches!(terminator.kind, TerminatorKind::Call { .. })
}

/// Collect all place-uses for a statement from dataflow edges and operands.
fn collect_statement_uses<'tcx>(
    statement: &'tcx rustc_middle::mir::Statement<'tcx>,
    block: BasicBlock,
    statement_index: usize,
    flow: &DataflowGraph,
) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();

    // Collect def locals (we know there are defs — caller already checked)
    let def_locals = match &statement.kind {
        StatementKind::Assign(assign) => {
            let (place, _) = &**assign;
            vec![place.local]
        }
        StatementKind::StorageDead(local) => vec![*local],
        _ => Vec::new(),
    };

    for &local in &def_locals {
        for &edge_idx in &flow.node(local).in_edges {
            let edge = &flow.edges[edge_idx];
            if edge.block == block.as_usize() && edge.statement_index == statement_index {
                uses.insert_local(edge.src);
            }
        }
    }

    // Also collect uses directly from operands — the dataflow graph
    // creates synthetic nodes for field projections (e.g. _13.0),
    // so we need the direct operand uses to reach through.
    if let StatementKind::Assign(assign) = &statement.kind {
        let (_, rvalue) = &**assign;
        for operand in super::super::def_use::rvalue_operands(rvalue) {
            uses.extend(operand_uses(operand));
        }
    }

    uses
}
