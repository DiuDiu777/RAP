use super::{bug_records::*, drop::*};
use crate::analysis::{
    alias_analysis::default::graph::AliasGraph,
    ownedheap_analysis::OHAResultMap,
    path_analysis::graph::PathGraph,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use std::{fmt, vec::Vec};

/// We represent each target function with the `SafeDropGraph` struct and then perform analysis
/// based on the struct.
pub struct SafeDropGraph<'tcx> {
    pub alias_graph: AliasGraph<'tcx>,
    pub bug_records: BugRecords,
    pub drop_record: Vec<DropRecord>,
    // analysis of heap item
    pub adt_owner: OHAResultMap,
}

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, adt_owner: OHAResultMap) -> Self {
        let alias_graph = AliasGraph::new(tcx, def_id);
        let mut drop_record = Vec::<DropRecord>::new();
        for v in &alias_graph.values {
            drop_record.push(DropRecord::false_record(v.index));
        }

        SafeDropGraph {
            alias_graph,
            bug_records: BugRecords::new(),
            drop_record,
            adt_owner,
        }
    }

    pub fn from_path_graph(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        path_graph: PathGraph<'tcx>,
        adt_owner: OHAResultMap,
    ) -> Self {
        let alias_graph = AliasGraph::from_path_graph(tcx, def_id, path_graph);
        let mut drop_record = Vec::<DropRecord>::new();
        for v in &alias_graph.values {
            drop_record.push(DropRecord::false_record(v.index));
        }

        SafeDropGraph {
            alias_graph,
            bug_records: BugRecords::new(),
            drop_record,
            adt_owner,
        }
    }

    /// Ensure `drop_record` matches the current length of `alias_graph.values`.
    /// Call this after any alias operation that may create new value nodes
    /// (`projection`, `sync_field_alias`, `sync_father_alias`, `handle_fn_alias`, etc.).
    pub fn sync_drop_record(&mut self) {
        while self.drop_record.len() < self.alias_graph.values.len() {
            let new_idx = self.drop_record.len();
            let father = self.alias_graph.values[new_idx].father.clone();
            self.drop_record.push(if let Some(fi) = father {
                DropRecord::from(new_idx, &self.drop_record[fi.father_value_id])
            } else {
                DropRecord::false_record(new_idx)
            });
        }
    }
}

impl<'tcx> std::fmt::Display for SafeDropGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SafeDropGraph {{")?;
        writeln!(f, "  AliasGraph: {}", self.alias_graph)?;
        write!(f, "}}")
    }
}
