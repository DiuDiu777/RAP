//! Path-sensitive points-to analysis.
//!
//! Given a verification path (sequence of basic blocks), this module builds a
//! `PointsToGraph` that records for each pointer-like local the MIR place it
//! was derived from.  The graph is constructed by a single forward scan over
//! the MIR statements and terminators on the path, without requiring the full
//! `AbstractValue` / `StateFact` machinery of the verifier.
//!
//! # Edge sources
//! * `Rvalue::Ref`     — `&_x`  / `&mut _x`   → `_x`
//! * `Rvalue::RawPtr`  — `&raw const/mut _x`  → `_x`
//! * `ptr::add/sub/offset` / `as_ptr` / `into_raw` / `cast` / `from_raw_parts`
//!   / NonNull constructors / ownership reconstruction — return → arg 0

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    BasicBlock, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::TyCtxt;

use crate::helpers::mir_utils;
use crate::verify::{
    call_summary::fn_simulator,
    def_use::{PlaceBaseKey, PlaceKey},
};

/// A path-sensitive points-to graph: each entry maps a pointer-like
/// `PlaceKey` to the `PlaceKey` it was derived from.
#[derive(Clone, Debug, Default)]
pub struct PointsToGraph {
    edges: HashMap<PlaceKey, PlaceKey>,
}

impl PointsToGraph {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record that `pointer` was derived from `source`.
    pub fn insert(&mut self, pointer: PlaceKey, source: PlaceKey) {
        self.edges.insert(pointer, source);
    }

    /// Transitively resolve `place` to its ultimate origin by following
    /// edges until a fixed point or no further edge exists.  Each hop
    /// supports overlap semantics: if the exact place is not a key, the
    /// base local (without field projections) is tried.
    pub fn resolve(&self, place: &PlaceKey) -> PlaceKey {
        let mut cur = place.clone();
        let mut seen: Vec<PlaceKey> = vec![cur.clone()];
        loop {
            let Some(next) = self.get_source(&cur) else {
                break;
            };
            if seen.iter().any(|p| p == next) {
                break;
            }
            seen.push(next.clone());
            cur = next.clone();
        }
        cur
    }

    /// Return the raw edges for external inspection / debugging.
    pub fn edges(&self) -> &HashMap<PlaceKey, PlaceKey> {
        &self.edges
    }

    /// Return the single-step source for `place`, supporting overlap
    /// semantics: if the exact place is not found, strip field projections
    /// and retry on the base local.
    pub fn get_source(&self, place: &PlaceKey) -> Option<&PlaceKey> {
        if let Some(source) = self.edges.get(place) {
            return Some(source);
        }
        if !place.fields.is_empty() {
            let base = PlaceKey {
                base: place.base.clone(),
                fields: Vec::new(),
            };
            return self.edges.get(&base);
        }
        None
    }
}

/// Build a points-to graph for `def_id` on the given forward path.
///
/// `path` is an ordered sequence of basic blocks from function entry to the
/// checkpoint location (excluding the checkpoint `PathStep::Checkpoint`).
pub fn build_points_to_graph<'tcx>(
    tcx: TyCtxt<'tcx>,
    path: &[BasicBlock],
    def_id: DefId,
) -> PointsToGraph {
    let body = tcx.optimized_mir(def_id);
    let mut graph = PointsToGraph::new();

    for &bb in path {
        let data = match body.basic_blocks.get(bb) {
            Some(data) => data,
            None => continue,
        };

        // ── Statements ────────────────────────────────────────────
        for stmt in &data.statements {
            let (place, rvalue) = match &stmt.kind {
                StatementKind::Assign(inner) => (&inner.0, &inner.1),
                _ => continue,
            };
            let target = PlaceKey::from_mir_place(place);

            match rvalue {
                Rvalue::Ref(_, _, source) => {
                    graph.insert(target, PlaceKey::from_mir_place(source));
                }
                Rvalue::RawPtr(_, source) => {
                    graph.insert(target, PlaceKey::from_mir_place(source));
                }
                _ => {}
            }
        }

        // ── Terminator (calls) ────────────────────────────────────
        if let Some(terminator) = &data.terminator {
            if let TerminatorKind::Call { func, args, destination, .. } = &terminator.kind {
                let name = mir_utils::call_name(tcx, func);
                let dest = PlaceKey {
                    base: PlaceBaseKey::Local(destination.local.as_usize()),
                    fields: Vec::new(),
                };

                if let Some(arg_ix) = pointer_return_arg(&name) {
                    if let Some(arg) = args.get(arg_ix) {
                        match &arg.node {
                            Operand::Copy(place) | Operand::Move(place) => {
                                graph.insert(dest, PlaceKey::from_mir_place(place));
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    graph
}

/// Return `Some(arg_index)` when the callee name corresponds to an API whose
/// return value is a pointer derived from that argument.  The lookup uses the
/// same name matchers as [`fn_simulator`], so it stays in sync with the
/// verifier's call-effect infrastructure.
fn pointer_return_arg(name: &str) -> Option<usize> {
    use fn_simulator::{
        is_as_ptr, is_as_ptr_range, is_as_mut_ptr_range, is_from_raw_parts,
        is_ownership_reconstruction, is_pointer_arithmetic, is_ptr_cast,
    };

    if is_as_ptr(name)
        || is_as_ptr_range(name)
        || is_as_mut_ptr_range(name)
        || is_pointer_arithmetic(name)
        || is_ptr_cast(name)
        || is_ownership_reconstruction(name)
        || is_from_raw_parts(name)
    {
        return Some(0);
    }

    // NonNull constructors
    if name.ends_with("::from") && name.contains("ptr::non_null")
        || name.ends_with("::new_unchecked") && name.contains("ptr::non_null")
        || name.ends_with("::as_ref") && name.contains("ptr::non_null")
        || name.ends_with("::as_mut") && name.contains("ptr::non_null")
    {
        return Some(0);
    }

    // split_at — returns two sub-slices that alias the original
    if name.contains("::split_at") {
        return Some(0);
    }

    // from_trait_call (core::convert::From::from) — may wrap NonNull
    if name == "std::convert::From::from" || name == "core::convert::From::from" {
        return Some(0);
    }

    None
}
