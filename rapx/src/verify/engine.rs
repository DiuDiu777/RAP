//! Symbolic-VM-based verification engine.
//!
//! Uses a semantic MIR executor to build symbolic state,
//! then checks safety properties with a unified property checker.

use z3::Config;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::path::PathTree;

use super::{
    contract::Property,
    report::CheckResult,
    slicer::{BackwardItem, BackwardSlicer},
};
use crate::helpers::mir_scan::{Checkpoint, CheckpointLocation};

use super::{vm::SymbolicVm, property_checker::PropertyChecker};

pub struct VerifyEngine<'tcx> {
    slicer: BackwardSlicer<'tcx>,
    vm: SymbolicVm<'tcx>,
    checker: PropertyChecker,
}

impl<'tcx> VerifyEngine<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            slicer: BackwardSlicer::new(tcx),
            vm: SymbolicVm::new(tcx),
            checker: PropertyChecker,
        }
    }

    pub fn check_callsite_from_tree(
        &self,
        tree: &PathTree,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        caller_contracts: &[Property<'tcx>],
    ) -> Vec<(CheckResult, String)> {
        let target_block = checkpoint.block.as_usize();
        let mut results = Vec::new();
        let backward_items = self
            .slicer
            .visit_path_tree(tree, target_block, checkpoint, property);

        let bound_property = Self::bind_property_to_checkpoint(property, checkpoint);

        let cfg = Config::new();
        let ctx = z3::Context::new(&cfg);

        for mut backward in backward_items {
            let path_desc = backward.path.describe_indices();

            if !caller_contracts.is_empty() {
                let mut all_items: Vec<BackwardItem<'tcx>> = caller_contracts
                    .iter()
                    .filter(|c| !matches!(c.kind, super::contract::PropertyKind::Unknown))
                    .map(|c| BackwardItem::ContractFact {
                        property: c.clone(),
                    })
                    .collect();
                all_items.extend(backward.items.drain(..));
                backward.items = all_items;
            }

            let vm_state = match self.vm.execute(&ctx, &backward) {
                Ok(state) => state,
                Err(reason) => {
                    results.push((CheckResult::Unknown, format!("{} (vm error: {})", path_desc, reason.message)));
                    continue;
                }
            };

            let result = self.checker.check(&vm_state, checkpoint, &bound_property);
            results.push((result, path_desc));
        }

        results
    }

    fn bind_property_to_checkpoint(
        property: &Property<'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> Property<'tcx> {
        let new_args: Vec<super::contract::PropertyArg<'tcx>> = property.args.iter()
            .map(|a| {
                match a {
                    super::contract::PropertyArg::Place(place) => {
                        super::contract::PropertyArg::Place(Self::rebind_place(place, checkpoint))
                    }
                    super::contract::PropertyArg::Expr(super::contract::ContractExpr::Place(place)) => {
                        super::contract::PropertyArg::Expr(super::contract::ContractExpr::Place(
                            Self::rebind_place(place, checkpoint),
                        ))
                    }
                    _ => a.clone(),
                }
            })
            .collect();

        let new_alternatives: Vec<Vec<Box<Property<'tcx>>>> = property.or_alternatives.iter().map(|group| {
            group.iter().map(|p| {
                Box::new(Self::bind_property_to_checkpoint(p, checkpoint))
            }).collect()
        }).collect();

        Property {
            kind: property.kind.clone(),
            args: new_args,
            contract_kind: property.contract_kind,
            null_guard: property.null_guard.clone(),
            or_alternatives: new_alternatives,
            for_each: property.for_each.clone(),
        }
    }

    fn rebind_place(
        place: &super::contract::ContractPlace<'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> super::contract::ContractPlace<'tcx> {
        let new_base = match place.base {
            super::contract::PlaceBase::Return => super::contract::PlaceBase::Return,
            super::contract::PlaceBase::Arg(n) => super::contract::PlaceBase::Arg(n),
            super::contract::PlaceBase::Local(n) => {
                if n > 0 && n <= checkpoint.args.len() {
                    super::contract::PlaceBase::Arg(n - 1)
                } else {
                    super::contract::PlaceBase::Local(n)
                }
            }
        };
        super::contract::ContractPlace {
            base: new_base,
            projections: place.projections.clone(),
        }
    }

    pub fn check_invariant_from_tree(
        &self,
        def_id: DefId,
        tree: &PathTree,
        checkpoint: CheckpointLocation,
        invariant: &Property<'tcx>,
        entry_facts: &[BackwardItem<'tcx>],
    ) -> Vec<(CheckResult, String)> {
        let target_block = checkpoint.block.as_usize();
        let mut results = Vec::new();
        let backward_items = self.slicer.visit_path_tree_for_checkpoint(
            tree,
            target_block,
            def_id,
            checkpoint,
            invariant,
        );

        let cfg = Config::new();
        let ctx = z3::Context::new(&cfg);

        for mut backward in backward_items {
            let path_desc = backward.path.describe_indices();

            if !entry_facts.is_empty() {
                let mut items: Vec<BackwardItem<'tcx>> = entry_facts.to_vec();
                items.extend(backward.items.drain(..));
                backward.items = items;
            }

            let vm_state = match self.vm.execute(&ctx, &backward) {
                Ok(state) => state,
                Err(reason) => {
                    results.push((CheckResult::Unknown, format!("{} (vm error: {})", path_desc, reason.message)));
                    continue;
                }
            };

            let fake_checkpoint = Checkpoint {
                caller: def_id,
                callee: None,
                block: checkpoint.block,
                span: rustc_span::DUMMY_SP,
                args: Vec::new(),
                kind: crate::helpers::mir_scan::CheckpointKind::UnsafeCall,
                is_ref: false,
                is_mut_ref: false,
                destination: None,
            };
            let result = self.checker.check(&vm_state, &fake_checkpoint, invariant);
            results.push((result, path_desc));
        }

        results
    }
}
