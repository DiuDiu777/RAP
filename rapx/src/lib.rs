#![feature(rustc_private)]
#![feature(box_patterns)]

#[macro_use]
pub mod utils;
pub mod analysis;

extern crate intervals;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate stable_mir;

use analysis::{
    core::{
        alias_analysis::default::AliasAnalyzer,
        api_dependency::default::ApiDependencyAnalyzer,
        callgraph::{default::CallGraphAnalyzer, CallGraphAnalysis, CallGraphDisplay},
        dataflow::DataFlowAnalyzer,
        ownedheap_analysis::{default::OwnedHeapAnalyzer, OwnedHeapAnalysis},
        range_analysis::default::RangeAnalyzer,
        ssa_transform::SSATrans,
    },
    opt::Opt,
    rcanary::rCanary,
    safedrop::SafeDrop,
    senryx::{CheckLevel, SenryxCheck},
    test::Test,
    unsafety_isolation::{UigInstruction, UnsafetyIsolationCheck},
    utils::show_mir::ShowMir,
    Analysis,
};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Config};
use rustc_middle::{ty::TyCtxt, util::Providers};
use rustc_session::search_paths::PathKind;
use std::path::PathBuf;
use std::{env, sync::Arc};

// Insert rustc arguments at the beginning of the argument list that RAP wants to be
// set per default, for maximal validation power.
pub static RAP_DEFAULT_ARGS: &[&str] = &["-Zalways-encode-mir", "-Zmir-opt-level=0"];

/// This is the data structure to handle rapx options as a rustc callback.

#[derive(Debug, Copy, Clone, Hash)]
pub struct RapCallback {
    alias: bool,
    api_dependency: bool,
    callgraph: bool,
    dataflow: usize,
    ownedheap: bool,
    range: usize,
    ssa: bool,
    test: bool,
    infer: bool,
    opt: usize,
    rcanary: bool,
    safedrop: bool,
    show_mir: bool,
    unsafety_isolation: usize,
    verify: bool,
}

#[allow(clippy::derivable_impls)]
impl Default for RapCallback {
    fn default() -> Self {
        Self {
            alias: false,
            api_dependency: false,
            callgraph: false,
            dataflow: 0,
            ownedheap: false,
            range: 0,
            ssa: false,
            test: false,
            infer: false,
            opt: usize::MAX,
            rcanary: false,
            safedrop: false,
            show_mir: false,
            unsafety_isolation: 0,
            verify: false,
        }
    }
}

impl Callbacks for RapCallback {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, providers| {
            providers.extern_queries.used_crate_source = |tcx, cnum| {
                let mut providers = Providers::default();
                rustc_metadata::provide(&mut providers);
                let mut crate_source = (providers.extern_queries.used_crate_source)(tcx, cnum);
                // HACK: rustc will emit "crate ... required to be available in rlib format, but
                // was not found in this form" errors once we use `tcx.dependency_formats()` if
                // there's no rlib provided, so setting a dummy path here to workaround those errors.
                Arc::make_mut(&mut crate_source).rlib = Some((PathBuf::new(), PathKind::All));
                crate_source
            };
        });
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        rap_trace!("Execute after_analysis() of compiler callbacks");
        start_analyzer(tcx, *self);
        rap_trace!("analysis done");
        Compilation::Continue
    }
}

impl RapCallback {
    /// Enable alias analysis. The parameter is used to config the threshold of alias analysis.
    /// Currently, we mainly use it to control the depth of field-sensitive analysis.
    /// -alias0: set field depth limit to 10; do not distinguish different flows within a each
    /// strongly-connected component.
    /// -alias1: set field depth limit to 20 (this is default setting).
    /// -alias2: set field depth limit to 30.
    pub fn enable_alias(&mut self, arg: String) {
        self.alias = true;
        match arg.as_str() {
            "-alias" => {
                env::set_var("ALIAS", "1");
            }
            "-alias0" => {
                env::set_var("ALIAS", "0");
            }
            "-alias1" => {
                env::set_var("ALIAS", "1");
            }
            "-alias2" => {
                env::set_var("ALIAS", "2");
            }
            _ => {}
        }
    }

    /// Test if alias analysis is enabled.
    pub fn is_alias_enabled(&self) -> bool {
        self.alias
    }

    /// Enable API-dependency graph generation.
    pub fn enable_api_dependency(&mut self) {
        self.api_dependency = true;
    }

    /// Test if API-dependency graph generation is enabled.
    pub fn is_api_dependency_enabled(self) -> bool {
        self.api_dependency
    }

    /// Enable call-graph analysis.
    pub fn enable_callgraph(&mut self) {
        self.callgraph = true;
    }

    /// Test if call-graph analysis is enabled.
    pub fn is_callgraph_enabled(&self) -> bool {
        self.callgraph
    }

    /// Enable owned heap analysis.
    pub fn enable_ownedheap(&mut self) {
        self.ownedheap = true;
    }

    /// Test if owned-heap analysis is enabled.
    pub fn is_ownedheap_enabled(self) -> bool {
        self.ownedheap
    }

    /// Enable dataflow analysis.
    pub fn enable_dataflow(&mut self, x: usize) {
        self.dataflow = x;
    }

    /// Test if dataflow analysis is enabled.
    pub fn is_dataflow_enabled(self) -> usize {
        self.dataflow
    }

    /// Enable range analysis.
    pub fn enable_range_analysis(&mut self, x: usize) {
        self.range = x;
    }

    /// Test if range analysis is enabled.
    pub fn is_range_analysis_enabled(self) -> bool {
        self.range > 0
    }

    /// Enable test of features provided by the core analysis traits.
    pub fn enable_test(&mut self) {
        self.test = true;
    }

    /// Check if test is enabled.
    pub fn is_test_enabled(self) -> bool {
        self.test
    }

    /// Enable ssa transformation
    pub fn enable_ssa_transform(&mut self) {
        self.ssa = true;
    }

    /// Test if ssa transformation is enabled.
    pub fn is_ssa_transform_enabled(self) -> bool {
        self.ssa
    }

    /// Enable optimization analysis for performance bug detection.
    pub fn enable_opt(&mut self, x: usize) {
        self.opt = x;
    }

    /// Test if optimization analysis is enabled.
    pub fn is_opt_enabled(self) -> usize {
        self.opt
    }

    /// Enable rcanary for memory leakage detection.
    pub fn enable_rcanary(&mut self) {
        self.rcanary = true;
    }

    /// Test if rcanary is enabled.
    pub fn is_rcanary_enabled(&self) -> bool {
        self.rcanary
    }

    /// Enable safedrop for use-after-free bug detection.
    /// Similar to alias analysis, the second parameter is to control the depth threshold for
    /// field-sensitive analysis.
    pub fn enable_safedrop(&mut self, arg: String) {
        self.safedrop = true;
        match arg.as_str() {
            "-F" => {
                env::set_var("SAFEDROP", "1");
                env::set_var("MOP", "1");
            }
            "-F0" => {
                env::set_var("SAFEDROP", "0");
                env::set_var("MOP", "0");
            }
            "-F1" => {
                env::set_var("SAFEDROP", "1");
                env::set_var("MOP", "1");
            }
            "-F2" => {
                env::set_var("SAFEDROP", "2");
                env::set_var("MOP", "2");
            }
            "-uaf" => {
                env::set_var("SAFEDROP", "1");
                env::set_var("MOP", "1");
            }
            _ => {}
        }
    }

    /// Test if safedrop is enabled.
    pub fn is_safedrop_enabled(&self) -> bool {
        self.safedrop
    }

    /// Enable mir display.
    pub fn enable_show_mir(&mut self) {
        self.show_mir = true;
    }

    /// Test if mir display is enabled.
    pub fn is_show_mir_enabled(&self) -> bool {
        self.show_mir
    }

    pub fn enable_unsafety_isolation(&mut self, x: usize) {
        self.unsafety_isolation = x;
    }

    pub fn is_unsafety_isolation_enabled(&self) -> usize {
        self.unsafety_isolation
    }

    pub fn enable_verify(&mut self) {
        self.verify = true;
    }

    pub fn is_verify_enabled(&self) -> bool {
        self.verify
    }

    pub fn enable_infer(&mut self) {
        self.infer = true;
    }

    pub fn is_infer_enabled(&self) -> bool {
        self.infer
    }
}

/// Start the analysis with the features enabled.
pub fn start_analyzer(tcx: TyCtxt, callback: RapCallback) {
    if callback.is_alias_enabled() {
        let mut analyzer = AliasAnalyzer::new(tcx);
        analyzer.run();
    }

    if callback.is_api_dependency_enabled() {
        let mut analyzer = ApiDependencyAnalyzer::new(tcx);
        analyzer.run();
    }

    if callback.is_callgraph_enabled() {
        let mut analyzer = CallGraphAnalyzer::new(tcx);
        analyzer.run();
        let callgraph = analyzer.get_callgraph();
        rap_info!(
            "{}",
            CallGraphDisplay {
                graph: &callgraph,
                tcx
            }
        );
        //analyzer.display();
    }

    match callback.is_dataflow_enabled() {
        1 => DataFlowAnalyzer::new(tcx, false).run(),
        2 => DataFlowAnalyzer::new(tcx, true).run(),
        _ => {}
    }

    if callback.is_ownedheap_enabled() {
        let mut analyzer = OwnedHeapAnalyzer::new(tcx);
        analyzer.run();
        analyzer.output();
    }

    if callback.is_range_analysis_enabled() {
        match callback.range {
            1 => {
                let mut analyzer = RangeAnalyzer::<i128>::new(tcx, false);
                analyzer.run();
            }
            2 => {
                let mut analyzer = RangeAnalyzer::<i128>::new(tcx, true);
                analyzer.run();
                analyzer.use_path_constraints_analysis();
            }
            _ => {}
        }
    }

    if callback.is_test_enabled() {
        let test = Test::new(tcx);
        test.start();
    }

    match callback.is_opt_enabled() {
        0 => Opt::new(tcx, 0).start(),
        1 => Opt::new(tcx, 1).start(),
        2 => Opt::new(tcx, 2).start(),
        _ => {}
    }

    let _rcanary: Option<rCanary> = if callback.is_rcanary_enabled() {
        let mut heap = OwnedHeapAnalyzer::new(tcx);
        heap.run();
        let adt_owner = heap.get_all_items();
        let mut rcx = rCanary::new(tcx, adt_owner);
        rcx.start();
        Some(rcx)
    } else {
        None
    };

    if callback.is_safedrop_enabled() {
        SafeDrop::new(tcx).start();
    }

    if callback.is_show_mir_enabled() {
        ShowMir::new(tcx).start();
    }

    if callback.is_ssa_transform_enabled() {
        SSATrans::new(tcx, false).start();
    }

    let x = callback.is_unsafety_isolation_enabled();
    match x {
        1 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::StdSp),
        2 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::Doc),
        3 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::Upg),
        4 => UnsafetyIsolationCheck::new(tcx).start(UigInstruction::Ucons),
        _ => {}
    }

    if callback.is_verify_enabled() {
        let check_level = CheckLevel::Medium;
        SenryxCheck::new(tcx, 2).start(check_level, true);
    }

    if callback.is_infer_enabled() {
        let check_level = CheckLevel::Medium;
        SenryxCheck::new(tcx, 2).start(check_level, false);
    }
}
