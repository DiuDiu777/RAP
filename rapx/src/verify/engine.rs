//! Shared verification engine for the staged verifier pipeline.
//!
//! This module extracts the common backward-visit → forward-visit → SMT-check
//! flow that is shared between unsafe-callsite verification and struct-invariant
//! verification, keeping both pipelines thin and focused on their own
//! path-preparation logic.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::path_analysis::PathTree;

use super::{
    contract::Property,
    forward_visit::{ForwardVisitResult, ForwardVerifier},
    helpers::Callsite,
    path::Path,
    path_refine::{BackwardItem, BackwardSlicer},
    report::CheckResult,
    smt_check::{SmtCheckResult, SmtChecker},
};

/// Result of checking one invariant along one reachability path.
pub struct InvariantCheckResult {
    /// Whether the invariant was proved, violated, or undecided.
    pub result: CheckResult,
    /// Backward slicing summary (MIR items kept along this path).
    pub slicing_diag: String,
    /// Combined forward verification and SMT check summary.
    pub verification_diag: String,
}

/// Thin wrapper around the three-stage verification pipeline.
///
/// Each structural check (callsite or invariant) delegates to one of the two
/// public methods; the engine handles visitor bookkeeping internally.
pub struct VerifyEngine<'tcx> {
    backward: BackwardSlicer<'tcx>,
    forward: ForwardVerifier<'tcx>,
    smt: SmtChecker<'tcx>,
}

impl<'tcx> VerifyEngine<'tcx> {
    /// Create an engine for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            backward: BackwardSlicer::new(tcx),
            forward: ForwardVerifier::new(tcx),
            smt: SmtChecker::new(tcx),
        }
    }

    /// Run the full pipeline for one struct-invariant checkpoint check.
    ///
    /// The checkpoint is derived from `path.target` — the callsite location at
    /// the end of the path.  `entry_facts` are prepended as `ContractFact`
    /// assumptions so the SMT model can treat them as already established at
    /// function entry.  The caller is responsible for assembling `entry_facts`
    /// (e.g. struct invariants for methods, or `#[rapx::requires]` contracts
    /// for constructors).
    ///
    /// # Parameters
    ///
    /// * `def_id` — the `DefId` of the function whose MIR body is being
    ///   verified.  Used to look up MIR data during backward analysis.
    /// * `path` — the reachability path from function entry to the checkpoint.
    ///   The checkpoint location is `path.target` (a `CallsiteLocation`
    ///   identifying the basic block and function containing the call
    ///   terminator).
    /// * `invariant` — the single `Property` to verify at the checkpoint
    ///   (e.g. one struct invariant).
    /// * `entry_facts` — pre-assembled `ContractFact` items that are assumed to
    ///   hold at function entry.  These are prepended to the backward-analysis
    ///   results so the forward simulation and SMT solver can use them as
    ///   given facts.
    pub fn check_invariant(
        &self,
        def_id: DefId,
        path: &Path,
        invariant: &Property<'tcx>,
        entry_facts: &[BackwardItem<'tcx>],
    ) -> InvariantCheckResult {
        let checkpoint = path.target;
        let mut backward = self
            .backward
            .visit_for_checkpoint(def_id, checkpoint, path, invariant);

        if !entry_facts.is_empty() {
            let mut items: Vec<BackwardItem<'tcx>> = entry_facts.to_vec();
            items.extend(backward.items.clone());
            backward.items = items;
        }

        let forward = self.forward.visit(&backward);
        let smt = self.smt.check_for_checkpoint(def_id, invariant, &forward);

        let tcx = self.backward.tcx();
        let slicing_diag = backward.describe_for_checkpoint(tcx, checkpoint, 0);
        let verification_diag = format!("{}\n{}", forward.describe(), smt.describe());

        InvariantCheckResult {
            result: smt.result,
            slicing_diag,
            verification_diag,
        }
    }

    /// Run the callsite-check pipeline in bulk using a shared path tree.
    ///
    /// Calls `visit_path_tree` once, then forward + SMT per path.
    pub fn check_callsite_from_tree(
        &self,
        tree: &PathTree,
        target_block: usize,
        callsite: &Callsite<'tcx>,
        property: &Property<'tcx>,
        caller_contracts: &[Property<'tcx>],
    ) -> Vec<(ForwardVisitResult<'tcx>, SmtCheckResult)> {
        let mut results = Vec::new();
        let backward_items = self
            .backward
            .visit_path_tree(tree, target_block, callsite, property);

        for mut backward in backward_items {
            if !caller_contracts.is_empty() {
                let mut items: Vec<BackwardItem<'tcx>> = caller_contracts
                    .iter()
                    .filter(|c| !matches!(c.kind, super::contract::PropertyKind::Unknown))
                    .map(|c| BackwardItem::ContractFact {
                        property: c.clone(),
                    })
                    .collect();
                items.extend(backward.items.clone());
                backward.items = items;
            }
            let forward = self.forward.visit(&backward);
            let smt = self.smt.check(callsite, property, &forward);
            results.push((forward, smt));
        }

        results
    }
}
