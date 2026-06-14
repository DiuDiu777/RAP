//! Driver utilities for the staged verifier pipeline.
//!
//! The target collector owns selected functions and their callee requirements.
//! The path extractor upgrades a function CFG into SCC-aware path metadata.
//! This module keeps those pieces together for one function target and exposes
//! callsite-level views for later backward visits, forward visits, and SMT stages.

use crate::analysis::Analysis;

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::TyCtxt;

use super::{
    contract::Property,
    forward_visit::ForwardVisitor,
    helpers::{Callsite, CallsiteLocation, collect_return_block_indices},
    path::{FunctionPaths, Path, PathExtractor},
    path_refine::BackwardVisitor,
    report::{PropertyCheckResult, VerificationReport, VisitDiagnostics},
    smt_check::SmtChecker,
    target::{FunctionTarget, VerifyTargetCollector},
};

/// Orchestrates verification inputs for one function target.
pub struct VerifyDriver<'target, 'tcx> {
    tcx: TyCtxt<'tcx>,
    target: &'target FunctionTarget<'tcx>,
    path_info: FunctionPaths<'tcx>,
    properties_to_verify: FxHashMap<super::helpers::CallsiteLocation, &'target [Property<'tcx>]>,
}

impl<'target, 'tcx> VerifyDriver<'target, 'tcx> {
    /// Build a driver for one collected function target.
    pub fn new(tcx: TyCtxt<'tcx>, target: &'target FunctionTarget<'tcx>) -> Self {
        Self::new_with_repeat(tcx, target, 0)
    }

    /// Build a driver with control over SCC postfix repeat count.
    pub fn new_with_repeat(
        tcx: TyCtxt<'tcx>,
        target: &'target FunctionTarget<'tcx>,
        allow_repeat: usize,
    ) -> Self {
        let path_info =
            PathExtractor::new(tcx, target.def_id, target.callsites.clone(), allow_repeat).run();
        let properties_to_verify = Self::build_properties_to_verify(target);
        Self {
            tcx,
            target,
            path_info,
            properties_to_verify,
        }
    }

    /// Return the compiler type context owned by this driver.
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Return the function target managed by this driver.
    pub fn target(&self) -> &'target FunctionTarget<'tcx> {
        self.target
    }

    /// Return the SCC-aware path metadata managed by this driver.
    pub fn path_info(&self) -> &FunctionPaths<'tcx> {
        &self.path_info
    }

    /// Run the current staged verifier pipeline for the managed function target.
    ///
    /// This method is the main driver entry for later verification stages.  It
    /// currently walks `(callsite, path, property)` items and records an
    /// `Unknown` result for each one. Backward visiting, forward visiting, and
    /// SMT checking can replace the placeholder result inside this loop without
    /// changing the surrounding control flow.
    pub fn verify_function(&self) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);
        let backward_visitor = BackwardVisitor::new(self.tcx);
        let forward_visitor = ForwardVisitor::new(self.tcx);
        let smt_checker = SmtChecker::new(self.tcx);

        for view in self.iter_callsite_checks() {
            for (path_index, path) in view.paths.iter().enumerate() {
                for (property_index, property) in view.properties.iter().enumerate() {
                    let backward = backward_visitor.visit(view.callsite, path, property);
                    let forward = forward_visitor.visit(&backward);
                    let smt_check = smt_checker.check(view.callsite, property, &forward);
                    let check_diagnostics =
                        format!("{}\n{}", forward.describe(), smt_check.describe());
                    report.push(PropertyCheckResult {
                        callsite: view.callsite.location(),
                        callsite_index: view.callsite_index,
                        path_index,
                        property_index,
                        property: property.clone(),
                        result: smt_check.result,
                        diagnostics: Some(VisitDiagnostics::new(
                            backward.describe(self.tcx, view.callsite, path_index),
                            check_diagnostics,
                        )),
                        path_description: path.describe_indices(),
                        callee_name: view.callsite.callee_name(self.tcx),
                    });
                }
            }
        }

        report
    }

    /// Return the required properties for a concrete unsafe callsite.
    pub fn properties_for_callsite(&self, callsite: &Callsite<'tcx>) -> &'target [Property<'tcx>] {
        self.properties_to_verify
            .get(&callsite.location())
            .copied()
            .unwrap_or(&[])
    }

    /// Iterate over callsites together with their paths and properties to verify.
    pub fn iter_callsite_checks(
        &self,
    ) -> impl Iterator<Item = CallsiteCheckView<'_, 'target, 'tcx>> + '_ {
        self.path_info
            .callsites()
            .iter()
            .filter_map(move |callsite| {
                let paths = self.path_info.paths_for(callsite.location());
                let properties = self.properties_for_callsite(callsite);
                if properties.is_empty() {
                    return None;
                }
                Some((callsite, paths, properties))
            })
            .enumerate()
            .map(
                move |(callsite_index, (callsite, paths, properties))| CallsiteCheckView {
                    callsite_index,
                    callsite,
                    paths,
                    properties,
                },
            )
    }

    /// Run struct invariant verification for the managed function target.
    ///
    /// For each return block in the function body, extracts paths from entry
    /// to that point and checks that each struct invariant holds.
    pub fn verify_struct_invariants(&self) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);
        let invariants = &self.target.struct_invariants;
        if invariants.is_empty() {
            return report;
        }

        let return_blocks = collect_return_block_indices(self.tcx, self.target.def_id);
        rap_info!(
            "[rapx::verify] struct invariant: {} return block(s) to check for {}",
            return_blocks.len(),
            self.tcx.def_path_str(self.target.def_id),
        );

        let backward_visitor = BackwardVisitor::new(self.tcx);
        let forward_visitor = ForwardVisitor::new(self.tcx);
        let smt_checker = SmtChecker::new(self.tcx);

        for &return_block in &return_blocks {
            let checkpoint = CallsiteLocation {
                caller: self.target.def_id,
                block: return_block,
            };

            let mut path_extractor = PathExtractor::new(
                self.tcx,
                self.target.def_id,
                Vec::new(),
                0, // struct invariants only use 0 repeats for now
            );
            let paths = path_extractor.find_paths_for_block(
                self.target.def_id,
                return_block,
            );

            rap_info!(
                "[rapx::verify] struct invariant checkpoint bb{}: {} reachable path(s)",
                return_block.as_usize(),
                paths.len()
            );

            for (path_index, path) in paths.iter().enumerate() {
                for (property_index, property) in invariants.iter().enumerate() {
                    rap_debug!(
                        "[rapx::verify] struct invariant path {} check: kind={:?}",
                        path_index,
                        property.kind
                    );

                    let backward = backward_visitor.visit_for_checkpoint(
                        self.target.def_id,
                        checkpoint,
                        path,
                        property,
                    );
                    let forward = forward_visitor.visit(&backward);
                    let smt_check = smt_checker.check_for_checkpoint(
                        self.target.def_id,
                        property,
                        &forward,
                    );
                    let check_diagnostics =
                        format!("{}\n{}", forward.describe(), smt_check.describe());

                    report.push(PropertyCheckResult {
                        callsite: checkpoint,
                        callsite_index: return_block.as_usize(),
                        path_index,
                        property_index,
                        property: property.clone(),
                        result: smt_check.result,
                        diagnostics: Some(VisitDiagnostics::new(
                            backward.describe_for_checkpoint(self.tcx, checkpoint, path_index),
                            check_diagnostics,
                        )),
                        path_description: path.describe_indices(),
                        callee_name: format!(
                            "struct-invariant(bb{})",
                            return_block.as_usize()
                        ),
                    });
                }
            }
        }

        report
    }

    /// Build the per-callsite property view from the target's callee requirements.
    fn build_properties_to_verify(
        target: &'target FunctionTarget<'tcx>,
    ) -> FxHashMap<super::helpers::CallsiteLocation, &'target [Property<'tcx>]> {
        target
            .callsites
            .iter()
            .map(|callsite| {
                let properties = target
                    .callee_requires
                    .get(&callsite.callee)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                (callsite.location(), properties)
            })
            .collect()
    }
}

/// Borrowed view of all verification inputs for one unsafe callsite.
pub struct CallsiteCheckView<'view, 'target, 'tcx> {
    /// Position among callsites that have properties to verify.
    pub callsite_index: usize,
    /// The concrete unsafe callsite in the caller MIR body.
    pub callsite: &'view Callsite<'tcx>,
    /// SCC-aware paths that can reach this callsite.
    pub paths: &'view [Path],
    /// Required safety properties for the unsafe callee.
    pub properties: &'target [Property<'tcx>],
}

/// Analysis pass that runs verification and emits function-level summaries.
pub struct VerifyRun<'tcx> {
    tcx: TyCtxt<'tcx>,
    allow_pathseg_repeat: usize,
}

impl<'tcx> VerifyRun<'tcx> {
    /// Create the default verify pass for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>, allow_pathseg_repeat: usize) -> Self {
        Self {
            tcx,
            allow_pathseg_repeat,
        }
    }
}

impl<'tcx> Analysis for VerifyRun<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Driver"
    }

    /// Collect verify targets, run the staged driver, and emit a compact summary.
    ///
    /// For each target, extracts paths with increasing `allow-pathseg-repeat`
    /// levels from 0 to the configured maximum, running verification at each
    /// level. Earlier rounds use fewer loop unrollings; later rounds incrementally
    /// add deeper paths.
    fn run(&mut self) {
        let mut collector = VerifyTargetCollector::new(self.tcx);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        for target in &collector.function_targets {
            let target_path = self.tcx.def_path_str(target.def_id);
            let mut combined_results: Vec<PropertyCheckResult<'_>> = Vec::new();

            // Phase 1: unsafe callsite verification
            for repeat in 0..=self.allow_pathseg_repeat {
                if self.allow_pathseg_repeat > 0 {
                    rap_info!(
                        "[rapx::verify] round {}/{}: allow-pathseg-repeat={}",
                        repeat,
                        self.allow_pathseg_repeat,
                        repeat
                    );
                }

                let driver = VerifyDriver::new_with_repeat(self.tcx, target, repeat);
                let report = driver.verify_function();
                let unproved = report
                    .results
                    .iter()
                    .filter(|result| !matches!(result.result, super::report::CheckResult::Proved))
                    .count();

                if unproved > 0 {
                    rap_warn!(
                        "[rapx::verify] round {}/{}: found {unproved} unproved check(s)",
                        repeat,
                        self.allow_pathseg_repeat
                    );
                }
                combined_results.extend(report.results);
            }

            // Phase 2: struct invariant verification
            if !target.struct_invariants.is_empty() {
                let driver = VerifyDriver::new(self.tcx, target);
                let struct_report = driver.verify_struct_invariants();
                combined_results.extend(struct_report.results);
            }

            let total = combined_results.len();
            let unproved = combined_results
                .iter()
                .filter(|result| !matches!(result.result, super::report::CheckResult::Proved))
                .count();

            if unproved == 0 {
                rap_info!("[rapx::verify] function: {target_path} | result: SOUND");
            } else {
                rap_warn!("[rapx::verify] function: {target_path} | result: UNSOUND");
                rap_debug!(
                    "[rapx::verify] function: {target_path} | checks not proved: {unproved}/{total}"
                );
                for result in &combined_results {
                    if !matches!(result.result, super::report::CheckResult::Proved) {
                        rap_info!(
                            "  [rapx::verify] callsite bb{} -> {}, path: {} | property {:?} | {:?}",
                            result.callsite.block.as_usize(),
                            result.callee_name,
                            result.path_description,
                            result.property.kind,
                            result.result,
                        );
                    }
                }
            }

            rap_debug!("Combined results: {} checks", combined_results.len());
        }
    }

    fn reset(&mut self) {}
}

/// Analysis pass that dumps backward and forward visitor diagnostics.
pub struct VerifyVisitDump<'tcx> {
    tcx: TyCtxt<'tcx>,
    allow_pathseg_repeat: usize,
}

impl<'tcx> VerifyVisitDump<'tcx> {
    /// Create a diagnostic dump pass for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>, allow_pathseg_repeat: usize) -> Self {
        Self {
            tcx,
            allow_pathseg_repeat,
        }
    }
}

impl<'tcx> Analysis for VerifyVisitDump<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Visitor Diagnostic Dump"
    }

    /// Collect verify targets and print the current staged visitor output.
    fn run(&mut self) {
        rap_debug!("======== #[rapx::verify] visitor diagnostics ========");
        let mut collector = VerifyTargetCollector::new(self.tcx);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        for target in &collector.function_targets {
            let target_path = self.tcx.def_path_str(target.def_id);
            rap_debug!(
                "[rapx::verify::diagnostics] target: {} (DefId: {:?})",
                target_path,
                target.def_id
            );

            for repeat in 0..=self.allow_pathseg_repeat {
                if self.allow_pathseg_repeat > 0 {
                    rap_debug!(
                        "[rapx::verify::diagnostics] round {}/{}: allow-pathseg-repeat={}",
                        repeat,
                        self.allow_pathseg_repeat,
                        repeat
                    );
                }
                let driver = VerifyDriver::new_with_repeat(self.tcx, target, repeat);
                let report = driver.verify_function();
                rap_debug!("{}", report.describe());
            }
        }

        rap_debug!("=======================================");
    }

    fn reset(&mut self) {}
}
