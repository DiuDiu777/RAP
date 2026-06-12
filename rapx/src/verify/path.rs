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
//! * **Outside SCC**: When the callsite lies outside any SCC, the extractor treats
//!   each SCC as a "black box" and emits a single step through one of its exit edges.
//!   This avoids unrolling and produces a bounded number of finite paths.
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

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};

use crate::analysis::path_analysis::graph::PathGraph;
use crate::graphs::scc::{SccRegion, find_scc_regions};

use super::helpers::{CFG, Callsite, CallsiteLocation};

const PATH_LIMIT: usize = 1024;

/// Mutable DFS state shared across recursive calls during entry-path search.
///
/// Used when the target callsite is **outside** any SCC region. The search starts
/// at the function entry and explores forward, treating SCCs as opaque by jumping
/// through one of their exit edges.
struct EntrySearchCtx<'a> {
    /// Set of blocks already visited on the current stack prefix (for cycle detection).
    visited: &'a mut FxHashSet<BasicBlock>,
    /// The current path stack being built during DFS.
    stack: &'a mut Vec<PathStep>,
    /// Accumulated complete paths that reach the target.
    results: &'a mut Vec<Path>,
    /// Maximum number of paths to produce before stopping the search.
    limit: usize,
    /// The location of the target callsite being searched for.
    target: CallsiteLocation,
    /// The MIR basic block that contains the target callsite.
    target_block: BasicBlock,
}

/// Mutable DFS state shared across recursive calls during entry-prefix search.
///
/// Used to find paths from the function entry to an SCC representative block,
/// going around other intervening SCCs via their exits. The results feed into
/// SCC-internal path construction as `entry_prefix` segments.
struct PrefixSearchCtx<'a> {
    /// Set of blocks already visited on the current stack prefix.
    visited: &'a mut FxHashSet<BasicBlock>,
    /// The current path stack being built during DFS.
    stack: &'a mut Vec<PathStep>,
    /// Accumulated prefix paths reaching the SCC representative.
    results: &'a mut Vec<Vec<PathStep>>,
    /// Maximum number of prefixes to produce.
    limit: usize,
    /// The SCC representative block to reach.
    representative: BasicBlock,
}

/// Mutable DFS state shared across recursive calls during SCC-internal path search.
///
/// Used when the target callsite is **inside** an SCC region. The search starts
/// at the SCC representative and explores only blocks within that SCC, enumerating
/// simple paths to the callsite. Each complete path is paired with every entry prefix
/// to produce full verification paths.
struct SccInternalCtx<'a> {
    /// Set of blocks already visited on the current stack prefix within the SCC.
    visited: &'a mut FxHashSet<BasicBlock>,
    /// The current path stack being built during DFS.
    stack: &'a mut Vec<PathStep>,
    /// Accumulated complete paths (body from representative to callsite).
    results: &'a mut Vec<Path>,
    /// Maximum number of paths to produce.
    limit: usize,
    /// The location of the target callsite.
    target: CallsiteLocation,
    /// The MIR basic block containing the target callsite.
    target_block: BasicBlock,
    /// The SCC representative (entry) block.
    representative: BasicBlock,
    /// The set of blocks belonging to this SCC.
    scc_blocks: &'a FxHashSet<BasicBlock>,
    /// Pre-computed entry prefixes from function entry to the representative.
    entry_prefixes: &'a [Vec<PathStep>],
}

/// Extracts SCC-aware, finite verification paths for one function body.
///
/// This is the main entry point for path extraction. It takes a function
/// (`def_id`) and its unsafe callsites, then:
///
/// 1. Detects SCC (loop) regions in the function CFG.
/// 2. For each callsite, enumerates finite paths either by treating SCCs as
///    opaque blocks or by computing entry-prefix + body-path pairs.
/// 3. Validates each path against a `PathGraph` for reachability.
///
/// The result is a `FunctionPaths` value that maps callsite locations to
/// their finite verification paths and exposes SCC region metadata.
pub struct PathExtractor<'tcx> {
    /// Compiler type context for MIR body access.
    tcx: TyCtxt<'tcx>,
    /// The function being analyzed.
    def_id: DefId,
    /// The function's control-flow graph (successor map).
    cfg: CFG,
    /// Unsafe callsites collected from the function body.
    callsites: Vec<Callsite<'tcx>>,
    /// SCC (strongly-connected component) regions detected in this function.
    scc_regions: Vec<SccRegion>,
    /// Maps each block to its SCC representative. Blocks not in any SCC are absent.
    block_to_scc: FxHashMap<BasicBlock, BasicBlock>,
    /// Extracted paths, keyed by callsite location.
    paths: FxHashMap<CallsiteLocation, Vec<Path>>,
    /// Lazily-initialized PathGraph for SCC path reachability checks.
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
            cfg: CFG::new(tcx, def_id),
            callsites,
            scc_regions: Vec::new(),
            block_to_scc: FxHashMap::default(),
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
        self.find_scc_regions();
        self.find_paths();
        FunctionPaths {
            scc_regions: SccRegions::new(self.scc_regions),
            callsite_paths: CallsitePaths::new(self.callsites, self.paths),
        }
    }

    /// Detect SCC regions in the function CFG and store their block-to-SCC map.
    ///
    /// Uses [`find_scc_regions`] from the graph module to identify
    /// strongly-connected components. Each SCC is assigned a representative
    /// (entry) block, and a reverse map from block to representative is built
    /// for fast lookups during path search.
    fn find_scc_regions(&mut self) {
        let (scc_regions, block_to_scc) = find_scc_regions(&self.cfg.successors);
        self.scc_regions = scc_regions;
        self.block_to_scc = block_to_scc;
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

    /// Extract paths for one callsite based on SCC membership.
    ///
    /// If the callsite block belongs to an SCC, we use
    /// [`find_scc_internal_paths`] which produces entry-prefix + body-path
    /// pairs. Otherwise we use [`find_entry_paths`] which treats SCCs as
    /// opaque and jumps through their exits.
    fn find_paths_for_callsite(&mut self, callsite: &Callsite<'tcx>) -> Vec<Path> {
        let target = callsite.location();
        if let Some(representative) = self.block_to_scc.get(&callsite.block).copied() {
            self.find_scc_internal_paths(representative, target, callsite.block)
        } else {
            self.find_entry_paths(target, callsite.block)
        }
    }

    // ── entry-path search (target outside SCC) ──────────────────────────
    //
    // These methods handle the case where the target callsite is not inside any
    // SCC. SCCs are treated as opaque: the search jumps from the SCC entry to
    // one of its exit blocks in a single logical step, without enumerating
    // internal SCC paths.

    /// Find all paths from the function entry to a callsite outside any SCC.
    ///
    /// Initializes a DFS from the entry block, with SCC regions treated as
    /// opaque via [`follow_scc_exits`]. The `target` and `target_block`
    /// identify the callsite to reach.
    fn find_entry_paths(&mut self, target: CallsiteLocation, target_block: BasicBlock) -> Vec<Path> {
        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(self.cfg.entry)];
        let mut visited = FxHashSet::default();
        visited.insert(self.cfg.entry);
        let mut ctx = EntrySearchCtx {
            visited: &mut visited,
            stack: &mut stack,
            results: &mut results,
            limit: PATH_LIMIT,
            target,
            target_block,
        };
        self.dfs_entry_paths(self.cfg.entry, &mut ctx);
        results
    }

    /// Depth-first search for paths from the entry to a callsite outside SCCs.
    ///
    /// When `current` equals `ctx.target_block`, a complete path is recorded
    /// (after a reachability check via `PathGraph`). SCC blocks are handled
    /// by [`follow_scc_exits`], which jumps through SCC exits as atomic steps.
    /// Non-SCC blocks are explored recursively with cycle detection.
    fn dfs_entry_paths(&mut self, current: BasicBlock, ctx: &mut EntrySearchCtx<'_>) {
        if ctx.results.len() >= ctx.limit {
            return;
        }

        if current == ctx.target_block {
            // Target reached: validate via PathGraph, then record the path.
            ctx.stack.push(PathStep::Callsite(ctx.target));
            let path_blocks: Vec<usize> = ctx
                .stack
                .iter()
                .filter_map(|s| match s {
                    PathStep::Block(bb) => Some(bb.as_usize()),
                    _ => None,
                })
                .collect();
            let reachable = self
                .path_graph()
                .is_path_reachable(&path_blocks);
            if reachable {
                ctx.results.push(Path {
                    target: ctx.target,
                    start: PathStart::FunctionEntry,
                    entry_prefix: Vec::new(),
                    steps: ctx.stack.clone(),
                });
            }
            ctx.stack.pop();
            return;
        }

        let successors = self.cfg.successors(current).to_vec();
        for &next in &successors {
            if ctx.results.len() >= ctx.limit {
                break;
            }

            let scc_rep = self.block_to_scc.get(&next).copied();
            if let Some(representative) = scc_rep {
                // Skip SCCs that contain both `next` and the target callsite —
                // they would be explored in the SCC-internal path search instead.
                let target_rep = self.block_to_scc.get(&ctx.target_block).copied();
                if target_rep == Some(representative) {
                    continue;
                }
                // Treat this SCC as opaque: jump through one of its exits.
                self.follow_scc_exits(next, representative, ctx);
                continue;
            }

            if ctx.visited.contains(&next) {
                continue;
            }

            ctx.stack.push(PathStep::Block(next));
            ctx.visited.insert(next);
            self.dfs_entry_paths(next, ctx);
            ctx.visited.remove(&next);
            ctx.stack.pop();
        }
    }

    /// Jump through an SCC by enumerating internal paths to each exit edge.
    ///
    /// For each exit edge `(from, to)` of the SCC, this method finds all
    /// simple paths from `entry` to `exit.from` within the SCC, then
    /// recursively continues the search from `exit.to`. The SCC-internal
    /// blocks are pushed onto the stack and visited set, then cleaned up
    /// after the recursive call returns (backtracking).
    ///
    /// If the SCC entry equals its representative, uses the `PathGraph`'s
    /// pre-computed SCC paths for efficiency.
    fn follow_scc_exits(
        &mut self,
        entry: BasicBlock,
        representative: BasicBlock,
        ctx: &mut EntrySearchCtx<'_>,
    ) {
        let scc_region = match self.scc_by_representative(representative) {
            Some(r) => r.clone(),
            None => return,
        };
        let scc_blocks: FxHashSet<BasicBlock> = scc_region.blocks.iter().copied().collect();

        for exit in scc_region.exits {
            if ctx.results.len() >= ctx.limit {
                break;
            }
            if ctx.visited.contains(&exit.to) {
                continue;
            }

            let internal_paths: Vec<Vec<BasicBlock>> = if entry == representative {
                let pg = self.path_graph();
                let scc_info = &pg.cfg.block(representative.as_usize()).scc;
                if scc_info.nodes.is_empty() {
                    vec![vec![entry]]
                } else {
                    let paths = pg.find_scc_paths(
                        representative.as_usize(),
                        &scc_info.clone(),
                        &FxHashMap::default(),
                    );
                    paths
                        .into_iter()
                        .map(|p| p.blocks.into_iter().map(|i| BasicBlock::from(i)).collect())
                        .collect()
                }
            } else {
                self.find_scc_paths_to(&scc_blocks, entry, exit.from, ctx.limit)
            };

            for internal_path in &internal_paths {
                if ctx.results.len() >= ctx.limit {
                    break;
                }

                let mut pushed: Vec<BasicBlock> = Vec::new();
                for &block in internal_path {
                    ctx.stack.push(PathStep::Block(block));
                    ctx.visited.insert(block);
                    pushed.push(block);
                }

                if ctx.visited.contains(&exit.to) {
                    for &block in pushed.iter().rev() {
                        ctx.visited.remove(&block);
                        ctx.stack.pop();
                    }
                    continue;
                }

                ctx.stack.push(PathStep::Block(exit.to));
                ctx.visited.insert(exit.to);
                self.dfs_entry_paths(exit.to, ctx);
                ctx.visited.remove(&exit.to);
                ctx.stack.pop();

                for &block in pushed.iter().rev() {
                    ctx.visited.remove(&block);
                    ctx.stack.pop();
                }
            }
        }
    }

    // ── entry-prefix search (to SCC representative) ─────────────────────
    //
    // These methods find paths from the function entry to an SCC
    // representative. The results are used as the `entry_prefix` segment of
    // SCC-internal paths. Other SCCs along the way are jumped through via
    // their exits, so the prefixes themselves remain finite.

    /// Find all paths from the function entry to a given SCC representative.
    ///
    /// Returns a list of prefix paths (sequences of `PathStep`s). If the
    /// entry block itself is the representative, returns a single empty prefix.
    /// If no paths are found, returns a single empty prefix as a fallback.
    fn find_entry_prefixes(&self, representative: BasicBlock, limit: usize) -> Vec<Vec<PathStep>> {
        if self.cfg.entry == representative {
            return vec![Vec::new()];
        }

        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(self.cfg.entry)];
        let mut visited = FxHashSet::default();
        visited.insert(self.cfg.entry);
        let mut ctx = PrefixSearchCtx {
            visited: &mut visited,
            stack: &mut stack,
            results: &mut results,
            limit,
            representative,
        };
        self.dfs_entry_prefixes(self.cfg.entry, &mut ctx);

        if results.is_empty() {
            vec![Vec::new()]
        } else {
            results
        }
    }

    /// DFS helper for finding entry prefixes to an SCC representative.
    ///
    /// Each time `next == ctx.representative`, the current stack is pushed as
    /// a complete prefix. When encountering another SCC, delegates to
    /// [`follow_scc_exits_for_prefix`] for opaque traversal. Cycle detection
    /// via `ctx.visited` prevents infinite recursion.
    fn dfs_entry_prefixes(&self, current: BasicBlock, ctx: &mut PrefixSearchCtx<'_>) {
        if ctx.results.len() >= ctx.limit {
            return;
        }

        for &next in self.cfg.successors(current) {
            if ctx.results.len() >= ctx.limit {
                break;
            }

            if next == ctx.representative {
                ctx.results.push(ctx.stack.clone());
                continue;
            }

            if let Some(scc_representative) = self.block_to_scc.get(&next).copied() {
                if scc_representative == ctx.representative {
                    continue;
                }
                self.follow_scc_exits_for_prefix(next, scc_representative, ctx);
                continue;
            }

            if ctx.visited.contains(&next) {
                continue;
            }

            ctx.stack.push(PathStep::Block(next));
            ctx.visited.insert(next);
            self.dfs_entry_prefixes(next, ctx);
            ctx.visited.remove(&next);
            ctx.stack.pop();
        }
    }

    /// Jump through an SCC during entry-prefix search.
    ///
    /// Works similarly to [`follow_scc_exits`] but targets the SCC
    /// representative instead of a callsite. For each exit edge, finds
    /// internal paths within the SCC from `entry` to `exit.from`, then
    /// continues the prefix search from `exit.to`.
    fn follow_scc_exits_for_prefix(
        &self,
        entry: BasicBlock,
        scc_representative: BasicBlock,
        ctx: &mut PrefixSearchCtx<'_>,
    ) {
        let Some(scc_info) = self.scc_by_representative(scc_representative) else {
            return;
        };
        let scc_blocks: FxHashSet<BasicBlock> = scc_info.blocks.iter().copied().collect();

        for exit in &scc_info.exits {
            if ctx.results.len() >= ctx.limit {
                break;
            }
            if ctx.visited.contains(&exit.to) {
                continue;
            }

            let internal_paths =
                self.find_scc_paths_to(&scc_blocks, entry, exit.from, ctx.limit);

            for internal_path in &internal_paths {
                if ctx.results.len() >= ctx.limit {
                    break;
                }

                let mut pushed: Vec<BasicBlock> = Vec::new();
                for &block in internal_path {
                    ctx.stack.push(PathStep::Block(block));
                    ctx.visited.insert(block);
                    pushed.push(block);
                }

                if ctx.visited.contains(&exit.to) {
                    for &block in pushed.iter().rev() {
                        ctx.visited.remove(&block);
                        ctx.stack.pop();
                    }
                    continue;
                }

                ctx.stack.push(PathStep::Block(exit.to));
                ctx.visited.insert(exit.to);
                self.dfs_entry_prefixes(exit.to, ctx);
                ctx.visited.remove(&exit.to);
                ctx.stack.pop();

                for &block in pushed.iter().rev() {
                    ctx.visited.remove(&block);
                    ctx.stack.pop();
                }
            }
        }
    }

    // ── SCC-internal path search ────────────────────────────────────────
    //
    // These methods handle the case where the target callsite is inside an
    // SCC. Two segments are produced:
    // 1. entry_prefix — from function entry to the SCC representative.
    // 2. body path — from the SCC representative to the callsite, staying
    //    within the SCC and using only simple (non-cyclic) paths.
    //
    // The full Path for verification is the concatenation:
    //   entry_prefix + body_path + callsite_step

    /// Build paths for a callsite that resides inside an SCC region.
    ///
    /// Computes entry prefixes via [`find_entry_prefixes`], then runs a DFS
    /// within the SCC from the representative to the callsite block. Each
    /// body path is paired with every entry prefix to produce all full
    /// verification paths.
    fn find_scc_internal_paths(
        &self,
        representative: BasicBlock,
        target: CallsiteLocation,
        target_block: BasicBlock,
    ) -> Vec<Path> {
        let Some(scc_info) = self.scc_by_representative(representative) else {
            return Vec::new();
        };
        let scc_blocks: FxHashSet<BasicBlock> = scc_info.blocks.iter().copied().collect();
        let entry_prefixes = self.find_entry_prefixes(representative, PATH_LIMIT);
        let mut results = Vec::new();
        let mut stack = vec![PathStep::Block(scc_info.representative)];
        let mut visited = FxHashSet::default();
        visited.insert(scc_info.representative);
        let mut ctx = SccInternalCtx {
            visited: &mut visited,
            stack: &mut stack,
            results: &mut results,
            limit: PATH_LIMIT,
            target,
            target_block,
            representative,
            scc_blocks: &scc_blocks,
            entry_prefixes: &entry_prefixes,
        };
        self.dfs_scc_internal_paths(scc_info.representative, &mut ctx);
        results
    }

    /// DFS within an SCC from the representative to the target callsite.
    ///
    /// Only blocks in `ctx.scc_blocks` are explored. When the target block
    /// is reached, a complete `Path` is recorded for each entry prefix.
    /// Standard DFS cycle detection prevents re-visiting SCC blocks on the
    /// current stack.
    fn dfs_scc_internal_paths(&self, current: BasicBlock, ctx: &mut SccInternalCtx<'_>) {
        if ctx.results.len() >= ctx.limit {
            return;
        }

        if current == ctx.target_block {
            ctx.stack.push(PathStep::Callsite(ctx.target));
            for entry_prefix in ctx.entry_prefixes {
                ctx.results.push(Path {
                    target: ctx.target,
                    start: PathStart::SccRepresentative {
                        representative: ctx.representative,
                    },
                    entry_prefix: entry_prefix.clone(),
                    steps: ctx.stack.clone(),
                });
                if ctx.results.len() >= ctx.limit {
                    break;
                }
            }
            ctx.stack.pop();
            return;
        }

        for &next in self.cfg.successors(current) {
            if !ctx.scc_blocks.contains(&next) || ctx.visited.contains(&next) {
                continue;
            }
            ctx.stack.push(PathStep::Block(next));
            ctx.visited.insert(next);
            self.dfs_scc_internal_paths(next, ctx);
            ctx.visited.remove(&next);
            ctx.stack.pop();
        }
    }

    /// Return the detected SCC region whose representative is `representative`.
    fn scc_by_representative(&self, representative: BasicBlock) -> Option<&SccRegion> {
        self.scc_regions
            .iter()
            .find(|scc_info| scc_info.representative == representative)
    }

    /// Find all simple paths from `from` to `to` within `scc_blocks` (endpoints included).
    fn find_scc_paths_to(
        &self,
        scc_blocks: &FxHashSet<BasicBlock>,
        from: BasicBlock,
        to: BasicBlock,
        limit: usize,
    ) -> Vec<Vec<BasicBlock>> {
        if from == to {
            return vec![vec![from]];
        }
        let mut results = Vec::new();
        let mut visited = FxHashSet::default();
        let mut stack = vec![from];
        visited.insert(from);
        self.dfs_scc_paths_to(scc_blocks, from, to, limit, &mut visited, &mut stack, &mut results);
        results
    }

    /// DFS helper for finding simple paths between two blocks within an SCC.
    ///
    /// Starting from `current`, explores successors within `scc_blocks`. When
    /// `next == target`, a complete path (stack + target) is pushed to results.
    /// Cycle detection prevents re-visiting blocks already on the stack.
    fn dfs_scc_paths_to(
        &self,
        scc_blocks: &FxHashSet<BasicBlock>,
        current: BasicBlock,
        target: BasicBlock,
        limit: usize,
        visited: &mut FxHashSet<BasicBlock>,
        stack: &mut Vec<BasicBlock>,
        results: &mut Vec<Vec<BasicBlock>>,
    ) {
        if results.len() >= limit {
            return;
        }

        for &next in self.cfg.successors(current) {
            if results.len() >= limit {
                break;
            }

            if next == target {
                let mut path = stack.clone();
                path.push(next);
                results.push(path);
                continue;
            }

            if !scc_blocks.contains(&next) || visited.contains(&next) {
                continue;
            }

            stack.push(next);
            visited.insert(next);
            self.dfs_scc_paths_to(scc_blocks, next, target, limit, visited, stack, results);
            visited.remove(&next);
            stack.pop();
        }
    }
}

/// Path metadata produced by a completed extraction run.
///
/// This is the path-level view of a function CFG: SCC-region information describes
/// cyclic regions, while callsite path information maps unsafe callsites to the
/// finite paths that reach them.
pub struct FunctionPaths<'tcx> {
    scc_regions: SccRegions,
    callsite_paths: CallsitePaths<'tcx>,
}

impl<'tcx> FunctionPaths<'tcx> {
    /// Return all callsites used during path extraction.
    pub fn callsites(&self) -> &[Callsite<'tcx>] {
        self.callsite_paths.callsites()
    }

    /// Return all SCC regions detected in the function CFG.
    pub fn scc_regions(&self) -> &[SccRegion] {
        self.scc_regions.scc_regions()
    }

    /// Return the paths extracted for one callsite location.
    pub fn paths_for(&self, location: CallsiteLocation) -> &[Path] {
        self.callsite_paths.paths_for(location)
    }
}

/// Metadata for SCC regions discovered in a function CFG.
///
/// Each SCC region represents a strongly-connected component (a loop or
/// mutually-recursive cycle) in the function's control-flow graph. The
/// regions are used by the verifier to reason about cyclic control flow
/// without unrolling it.
pub struct SccRegions {
    scc_regions: Vec<SccRegion>,
}

impl SccRegions {
    /// Create SCC-region metadata from detected SCC regions.
    fn new(scc_regions: Vec<SccRegion>) -> Self {
        Self { scc_regions }
    }

    /// Return all detected SCC regions.
    pub fn scc_regions(&self) -> &[SccRegion] {
        &self.scc_regions
    }
}

/// Metadata that maps unsafe callsites to finite verification paths.
///
/// Each callsite found during extraction is mapped to zero or more `Path`
/// instances. When no paths exist for a callsite, it means the callsite is
/// unreachable from the function entry (dead code).
pub struct CallsitePaths<'tcx> {
    callsites: Vec<Callsite<'tcx>>,
    paths_by_callsite: FxHashMap<CallsiteLocation, Vec<Path>>,
}

impl<'tcx> CallsitePaths<'tcx> {
    /// Create callsite path metadata from callsites and extracted paths.
    fn new(
        callsites: Vec<Callsite<'tcx>>,
        paths_by_callsite: FxHashMap<CallsiteLocation, Vec<Path>>,
    ) -> Self {
        Self {
            callsites,
            paths_by_callsite,
        }
    }

    /// Return all callsites used during path extraction.
    pub fn callsites(&self) -> &[Callsite<'tcx>] {
        &self.callsites
    }

    /// Return the paths extracted for one callsite location.
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
