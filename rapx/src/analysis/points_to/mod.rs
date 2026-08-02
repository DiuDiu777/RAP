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
//!
//! # New unified API
//!
//! The new `graph::PtsGraph` provides a richer points-to representation with:
//! * `assign_value(dest, src)` — value-copy tracking
//! * `assign_pointee(dest, target)` — direct points-to edges
//! * `pts(slot)` — transitive points-to query
//! * `may_alias(a, b)` — alias check as pts-intersection

pub mod builder;
pub mod graph;
pub mod slot;

use std::collections::HashMap;

use crate::verify::def_use::PlaceKey;

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


