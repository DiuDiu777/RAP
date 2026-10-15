//! Path extraction for verification targets.
//!
//! This module builds finite, acyclic paths from a function CFG to each unsafe checkpoint
//! so that the verifier can reason about pointer properties along concrete execution
//! traces without unrolling loops or recursive cycles.
//!
//! # Path reachability
//!
//! Each path is validated against a `PathGraph` (an SCC-aware path enumeration
//! structure) to ensure the computed block sequence is actually reachable. Paths
//! that fail this check are silently discarded.
//!
//! # Path limit
//!
//! To prevent exponential blow-up, path enumeration is capped at
//! [`crate::limit::path_limit`] (the `--path-limit` CLI value, or
//! [`crate::limit::PATH_LIMIT`]). Enumeration stops producing new paths once
//! the limit is reached and the tree is marked truncated.

use rustc_hir::def_id::DefId;
use rustc_middle::{mir::BasicBlock, ty::TyCtxt};

use crate::analysis::path::{
    PathTree,
    graph::{PathEnumerator, PathGraph},
};

use crate::verify::checkpoint::CheckpointLocation;

/// Enumerates finite, acyclic verification paths from function entry to each
/// unsafe checkpoint in one function body.
///
/// `run` builds a [`PathGraph`], inlines callees, finds SCCs, then enumerates
/// acyclic paths with `allow_repeat` extra loop iterations.  The resulting
/// [`PathTree`] holds all whole-CFG paths; checkpoints and struct invariants
/// slice their own prefixes from it via `walk_prefixes`/`subtree_to`.
///
/// Enumeration is capped at [`crate::limit::path_limit`] to avoid exponential
/// blow-up.
pub(crate) struct PathExtractor<'tcx> {
    /// Compiler type context used for MIR access and name resolution.
    tcx: TyCtxt<'tcx>,
    /// The function whose MIR body is being analyzed.
    def_id: DefId,
    /// Number of extra SCC postfix repetitions allowed (default 0).
    allow_repeat: usize,
}

impl<'tcx> PathExtractor<'tcx> {
    /// Create a path extractor for `def_id`.
    ///
    /// Path extraction (SCC detection, enumeration, filtering) is deferred
    /// until [`run`] is called.
    ///
    /// `allow_repeat` controls how many times a repeated SCC postfix segment
    /// is allowed beyond the first occurrence. Default is 0 (no extra repeats).
    pub(crate) fn new(tcx: TyCtxt<'tcx>, def_id: DefId, allow_repeat: usize) -> Self {
        Self {
            tcx,
            def_id,
            allow_repeat,
        }
    }

    /// Run path extraction, consuming the extractor.
    ///
    /// Returns the whole-CFG [`PathTree`], with inlined callees and the
    /// block-function metadata attached.
    pub(crate) fn run(self) -> PathTree {
        let mut graph = PathGraph::new(self.tcx, self.def_id);
        graph.inline_callees();
        graph.find_scc();
        let mut tree = {
            let mut enumerator = PathEnumerator::new(&graph);
            enumerator.enumerate_paths_repeat(self.allow_repeat)
        };
        tree.set_block_fn(
            graph
                .cfg
                .blocks
                .iter()
                .map(|b| (b.def_id, b.local_index))
                .collect(),
            graph.inline_bindings.clone(),
            graph.inline_parents.clone(),
            graph.inlined_call_blocks.clone(),
        );
        tree
    }
}

/// One finite, acyclic execution trace from function entry to a checkpoint,
/// represented as an ordered sequence of MIR basic blocks.
///
/// Built by the [`BackwardSlicer`](super::slicer::BackwardSlicer) from the
/// [`PathTree`] produced by [`PathExtractor`]; the VM later consumes it to
/// know which MIR instructions are relevant and in what order.
///
/// Every path is validated against the SCC-aware [`PathGraph`]; unreachable
/// sequences are silently discarded during extraction.
#[derive(Clone, Debug)]
pub(crate) struct Path {
    /// The [`CheckpointLocation`] (function + basic block) reached by this
    /// path, also recorded as the final `PathStep::Checkpoint`.
    pub target: CheckpointLocation,
    /// Ordered block sequence from function entry to `target`, terminated by a
    /// `PathStep::Checkpoint`.
    pub steps: Vec<PathStep>,
}

impl Path {
    /// Render this path as a compact array of block indices.
    pub(crate) fn describe_indices(&self) -> String {
        let mut indices: Vec<usize> = Vec::new();
        for step in &self.steps {
            match step {
                PathStep::Block(b) => indices.push(b.as_usize()),
                PathStep::Checkpoint(l) => {
                    let bb = l.block.as_usize();
                    if indices.last() != Some(&bb) {
                        indices.push(bb);
                    }
                }
            }
        }
        format!("{:?}", indices)
    }

}

/// One step in a finite verification path.
#[derive(Clone, Debug)]
pub(crate) enum PathStep {
    /// A normal MIR basic block.
    Block(BasicBlock),
    /// The target checkpoint that terminates the path.
    Checkpoint(CheckpointLocation),
}
