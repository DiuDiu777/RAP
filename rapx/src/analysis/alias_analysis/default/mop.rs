use rustc_hir::def_id::DefId;

use std::collections::HashSet;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use super::value::Value;
use super::{graph::*, *};

#[derive(Clone)]
struct MopStateSnapshot {
    values: Vec<Value>,
    constants: FxHashMap<usize, usize>,
    alias_sets: Vec<FxHashSet<usize>>,
}

impl<'tcx> AliasGraph<'tcx> {
    fn snapshot_state(&self) -> MopStateSnapshot {
        MopStateSnapshot {
            values: self.values.clone(),
            constants: self.constants.clone(),
            alias_sets: self.alias_sets.clone(),
        }
    }

    fn restore_state(&mut self, snapshot: &MopStateSnapshot) {
        self.values = snapshot.values.clone();
        self.constants = snapshot.constants.clone();
        self.alias_sets = snapshot.alias_sets.clone();
    }

    /// Process pre-enumerated whole-function paths.
    ///
    /// Each reachable path is traversed linearly from its starting block
    /// to its terminator.  State is restored from the initial snapshot
    /// before each path.  No recursive SCC handling is needed — the
    /// paths already contain every block in order.
    pub fn process_function_paths(
        &mut self,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let paths = self.path_graph.enumerate_paths();
        let initial_snapshot = self.snapshot_state();
        let initial_recursion = recursion_set.clone();

        for path in &paths {
            if !self.path_graph.is_path_reachable(path) {
                continue;
            }
            self.increment_visit_times();
            if self.visit_times() > VISIT_LIMIT {
                return;
            }

            self.restore_state(&initial_snapshot);
            *recursion_set = initial_recursion.clone();

            for &block in path {
                self.alias_bb(block);
                self.alias_bbcall(block, fn_map, recursion_set);
            }

            self.merge_results();
        }
    }
}
