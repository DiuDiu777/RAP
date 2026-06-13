//! Path extraction for verification targets.
//!
//! This module builds finite, acyclic paths from a function CFG to each unsafe callsite
//! so that the verifier can reason about pointer properties along concrete execution
//! traces without unrolling loops or recursive cycles.
//!
//! # Problem
//!
//! A MIR control-flow graph (CFG) may contain strongly-connected components (SCCs)
//! representing loops. Naively enumerating all paths through a loop yields infinitely
//! many traces, which is unsuitable for verification.
//!
//! # Solution overview
//!
//! The extractor detects SCC regions via `find_scc_regions` and handles them
//! differently depending on where the target callsite resides:
//!
//! * **Outside SCC**: When the callsite lies outside any SCC, the extractor
//!   fully expands each SCC by enumerating all simple paths through it via
//!   `PathGraph::find_scc_paths`, splicing their block sequences into the DFS
//!   trail. This produces a bounded number of finite paths.
//!
//! * **Inside SCC**: When the callsite itself is inside an SCC, the extractor
//!   computes two segments:
//!   1. An **entry prefix** — the path from the function entry to the SCC's
//!      representative (entry) block, going around other SCCs via their exits.
//!   2. A **body path** — the path from the SCC representative to the callsite,
//!      staying within the SCC. Only simple (non-cyclic) internal paths are
//!      enumerated.
//!
//!   This preserves definitions and facts (e.g. pointer initializations) established
//!   before the SCC region without unrolling cyclic control flow inside it.
//!
//! # Path reachability
//!
//! Each path is validated against a `PathGraph` (an SCC-aware path enumeration
//! structure) to ensure the computed block sequence is actually reachable. Paths
//! that fail this check are silently discarded.
//!
//! # Path limit
//!
//! To prevent exponential blow-up, path enumeration is capped at `PATH_LIMIT`
//! (currently 1024) per search. Searches stop producing new paths once the limit
//! is reached.

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};

use crate::analysis::path_analysis::graph::PathGraph;

use super::helpers::{Callsite, CallsiteLocation};

const PATH_LIMIT: usize = 1024;


/// Extracts SCC-aware, finite verification paths for one function body.
///
/// This is the main entry point for path extraction. It takes a function
/// (`def_id`) and its unsafe callsites, then:
///
/// 1. Detects SCC (loop) regions in the function CFG.
/// 2. For each callsite, enumerates finite paths by fully expanding SCCs
///    (via `PathGraph::find_scc_paths`) or by computing entry-prefix + body-path pairs.
/// 3. Validates each path against a `PathGraph` for reachability.
///
/// The result is a `FunctionPaths` value that maps callsite locations to
/// their finite verification paths and exposes SCC region metadata.
pub struct PathExtractor<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    callsites: Vec<Callsite<'tcx>>,
    paths: FxHashMap<CallsiteLocation, Vec<Path>>,
    path_graph: Option<PathGraph<'tcx>>,
}

impl<'tcx> PathExtractor<'tcx> {
    /// Create a path extractor for `def_id` and the callsites found in that body.
    ///
    /// This initializes the CFG and stores callsites. SCC detection and path
    /// extraction are deferred until [`run`] is called.
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, callsites: Vec<Callsite<'tcx>>) -> Self {
        Self {
            tcx,
            def_id,
            callsites,
            paths: FxHashMap::default(),
            path_graph: None,
        }
    }

    /// Get (or create) the PathGraph for this function's full SCC enumeration.
    fn path_graph(&mut self) -> &mut PathGraph<'tcx> {
        self.path_graph.get_or_insert_with(|| {
            let mut pg = PathGraph::new(self.tcx, self.def_id);
            pg.find_scc();
            pg
        })
    }

    /// Run SCC-region detection and path extraction, consuming the extractor.
    ///
    /// Returns a `FunctionPaths` value that bundles SCC metadata with the
    /// per-callsite path vectors. This is the main driver method.
    pub fn run(mut self) -> FunctionPaths<'tcx> {
        // Ensure PathGraph is initialized (also builds SCC info internally).
        self.path_graph();
        self.find_paths();
        FunctionPaths {
            callsite_paths: CallsitePaths::new(self.callsites, self.paths),
        }
    }

    /// Extract paths for every callsite owned by this extractor.
    ///
    /// Iterates over all callsites and delegates to [`find_paths_for_callsite`]
    /// for each one. Results are stored in `self.paths` keyed by callsite location.
    fn find_paths(&mut self) {
        for index in 0..self.callsites.len() {
            let callsite = self.callsites[index].clone();
            let paths = self.find_paths_for_callsite(&callsite);
            self.paths.insert(callsite.location(), paths);
        }
    }

    /// Extract paths for one callsite by filtering pre-enumerated whole-function paths.
    ///
    /// Uses `PathGraph::enumerate_paths()` to get all CFG paths, then filters
    /// to those containing the target callsite block and passing reachability.
    /// Paths are truncated at the target block (inclusive).
    fn find_paths_for_callsite(&mut self, callsite: &Callsite<'tcx>) -> Vec<Path> {
        let target = callsite.location();
        let target_block = callsite.block.as_usize();
        let pg = self.path_graph();
        let all_paths = pg.enumerate_paths();

        rap_info!(
            "Callsite at bb{}: {} whole-cfg paths",
            target_block, all_paths.len()
        );

        let mut results = Vec::new();
        for (idx, path) in all_paths.iter().enumerate() {
            if results.len() >= PATH_LIMIT {
                break;
            }
            let Some(pos) = path.iter().position(|&b| b == target_block) else {
                rap_info!("  whole-cfg path {}: {:?} | reachable: false (no target)", idx, path);
                continue;
            };
            let prefix: Vec<usize> = path[..=pos].to_vec();
            let reachable = pg.is_path_reachable(&prefix);
            rap_info!(
                "  verify path {}: {:?} | reachable: {}",
                idx, prefix, reachable
            );
            if !reachable {
                continue;
            }
            results.push(Path {
                target,
                start: PathStart::FunctionEntry,
                entry_prefix: Vec::new(),
                steps: prefix
                    .into_iter()
                    .map(|b| PathStep::Block(BasicBlock::from(b)))
                    .chain(std::iter::once(PathStep::Callsite(target)))
                    .collect(),
            });
        }
        results
    }
}

/// Result of path extraction for one function.
pub struct FunctionPaths<'tcx> {
    callsite_paths: CallsitePaths<'tcx>,
}

impl<'tcx> FunctionPaths<'tcx> {
    pub fn paths_for(&self, location: CallsiteLocation) -> &[Path] {
        self.callsite_paths.paths_for(location)
    }

    pub fn callsites(&self) -> &[Callsite<'tcx>] {
        self.callsite_paths.callsites()
    }
}

pub struct CallsitePaths<'tcx> {
    callsites: Vec<Callsite<'tcx>>,
    paths_by_callsite: FxHashMap<CallsiteLocation, Vec<Path>>,
}

impl<'tcx> CallsitePaths<'tcx> {
    fn new(
        callsites: Vec<Callsite<'tcx>>,
        paths_by_callsite: FxHashMap<CallsiteLocation, Vec<Path>>,
    ) -> Self {
        Self {
            callsites,
            paths_by_callsite,
        }
    }

    pub fn callsites(&self) -> &[Callsite<'tcx>] {
        &self.callsites
    }

    pub fn paths_for(&self, location: CallsiteLocation) -> &[Path] {
        self.paths_by_callsite
            .get(&location)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

/// A finite verification path reaching one callsite.
#[derive(Clone, Debug)]
pub struct Path {
    /// Callsite reached by this path.
    pub target: CallsiteLocation,
    /// Where the path starts.
    pub start: PathStart,
    /// Blocks from function entry to this path's start.
    ///
    /// This is currently non-empty for SCC-internal callsites. It preserves
    /// definitions established before the SCC representative without unrolling
    /// SCC-internal control flow.
    pub entry_prefix: Vec<PathStep>,
    /// Ordered steps from the start point to the target callsite.
    pub steps: Vec<PathStep>,
}

impl Path {
    /// Render this path as a compact string for diagnostics.
    pub fn describe(&self) -> String {
        let body = self
            .steps
            .iter()
            .map(describe_step)
            .collect::<Vec<_>>()
            .join(" -> ");

        if self.entry_prefix.is_empty() {
            return body;
        }

        format!("entry: {} | body: {}", self.describe_entry_prefix(), body)
    }

    /// Render the entry prefix and append the SCC representative when applicable.
    pub fn describe_entry_prefix(&self) -> String {
        let mut parts = self
            .entry_prefix
            .iter()
            .map(describe_step)
            .collect::<Vec<_>>();
        if let PathStart::SccRepresentative { representative } = self.start {
            parts.push(format!("bb{}", representative.as_usize()));
        }
        parts.join(" -> ")
    }

    /// Render only the path body from the start point to the callsite.
    pub fn describe_body(&self) -> String {
        self.steps
            .iter()
            .map(describe_step)
            .collect::<Vec<_>>()
            .join(" -> ")
    }
}

/// Render one path step as a human-readable string for diagnostics.
///
/// - `PathStep::Block(bb)`   -> `"bb<N>"`
/// - `PathStep::Callsite(l)` -> `"callsite(bb<N>)"`
fn describe_step(step: &PathStep) -> String {
    match step {
        PathStep::Block(bb) => format!("bb{}", bb.as_usize()),
        PathStep::Callsite(location) => {
            format!("callsite(bb{})", location.block.as_usize())
        }
    }
}

/// Start point for a finite verification path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PathStart {
    /// The path starts at the function entry block.
    FunctionEntry,
    /// The path starts at the representative of an SCC containing the target callsite.
    SccRepresentative { representative: BasicBlock },
}

/// One step in a finite verification path.
#[derive(Clone, Debug)]
pub enum PathStep {
    /// A normal MIR basic block.
    Block(BasicBlock),
    /// The target callsite that terminates the path.
    Callsite(CallsiteLocation),
}
