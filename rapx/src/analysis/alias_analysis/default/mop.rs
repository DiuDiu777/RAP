use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        Operand::{Constant, Copy, Move},
        TerminatorKind,
    },
    ty::{TyKind, TypingEnv},
};

use std::{cell::Cell, collections::HashSet};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use crate::{analysis::path_analysis::graph::SccEnumeratedPath, graphs::scc::SccInfo};

use super::value::Value;
use super::{graph::*, *};

/// rustc analysis threads can have a relatively small stack.
///
/// We cap recursive `check` depth so deeply nested CFG/SCC exploration degrades gracefully
/// instead of overflowing the compiler thread stack.
const CHECK_STACK_LIMIT: usize = 96;
thread_local! {
    static CHECK_DEPTH: Cell<usize> = Cell::new(0);
}

#[derive(Clone)]
struct MopStateSnapshot {
    values: Vec<Value>,
    constants: FxHashMap<usize, usize>,
    alias_sets: Vec<FxHashSet<usize>>,
}

enum SwitchSuccessorPlan {
    NotSwitch,
    SingleTarget {
        target: usize,
    },
    SplitTargets {
        constraint_id: usize,
        targets: rustc_middle::mir::SwitchTargets,
        otherwise_value: Option<usize>,
    },
}

struct DepthLimitGuard {
    key: &'static std::thread::LocalKey<Cell<usize>>,
}

fn enter_depth_limit(
    key: &'static std::thread::LocalKey<Cell<usize>>,
    limit: usize,
) -> Option<DepthLimitGuard> {
    key.with(|d| {
        let cur = d.get() + 1;
        d.set(cur);
        if cur > limit {
            d.set(cur - 1);
            None
        } else {
            Some(DepthLimitGuard { key })
        }
    })
}

impl Drop for DepthLimitGuard {
    fn drop(&mut self) {
        self.key.with(|d| {
            let cur = d.get();
            if cur > 0 {
                d.set(cur - 1);
            }
        });
    }
}

impl<'tcx> AliasGraph<'tcx> {
    pub(crate) fn is_path_reachable(&self, path: &[usize], initial: &FxHashMap<usize, usize>) -> bool {
        self.path_graph.is_path_reachable_with(path, initial)
    }

    fn switch_target_for_value(
        &self,
        targets: &rustc_middle::mir::SwitchTargets,
        value: usize,
    ) -> usize {
        for (v, bb) in targets.iter() {
            if v as usize == value {
                return bb.as_usize();
            }
        }
        targets.otherwise().as_usize()
    }

    fn unique_otherwise_switch_value(
        &self,
        discr: &rustc_middle::mir::Operand<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
    ) -> Option<usize> {
        let tcx = self.tcx();
        let local_decls = &tcx.optimized_mir(self.def_id()).local_decls;

        let place = match discr {
            Copy(p) | Move(p) => Some(*p),
            _ => None,
        }?;

        let place_ty = place.ty(local_decls, tcx).ty;
        let possible_values: Vec<usize> = match place_ty.kind() {
            TyKind::Bool => vec![0, 1],
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => (0..adt_def.variants().len()).collect(),
            _ => return None,
        };

        let mut seen = FxHashSet::default();
        for (val, _) in targets.iter() {
            seen.insert(val as usize);
        }

        let remaining: Vec<usize> = possible_values
            .into_iter()
            .filter(|v| !seen.contains(v))
            .collect();

        if remaining.len() == 1 {
            Some(remaining[0])
        } else {
            None
        }
    }

    fn possible_switch_values_for_constraint_id(&self, discr_local: usize) -> Option<Vec<usize>> {
        let tcx = self.tcx();
        let local_decls = &tcx.optimized_mir(self.def_id()).local_decls;
        if discr_local >= local_decls.len() {
            return None;
        }

        let ty = local_decls[rustc_middle::mir::Local::from_usize(discr_local)].ty;
        match ty.kind() {
            TyKind::Bool => Some(vec![0, 1]),
            TyKind::Adt(adt_def, _) if adt_def.is_enum() => {
                Some((0..adt_def.variants().len()).collect())
            }
            _ => None,
        }
    }

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

    fn known_switch_value(&mut self, discr: &rustc_middle::mir::Operand<'tcx>) -> Option<usize> {
        match discr {
            Copy(p) | Move(p) => {
                let value_idx = self.projection(*p);
                let tcx = self.tcx();
                let local_decls = &tcx.optimized_mir(self.def_id()).local_decls;
                let place_ty = (*p).ty(local_decls, tcx);

                match place_ty.ty.kind() {
                    TyKind::Bool => self
                        .constants
                        .get(&value_idx)
                        .copied()
                        .filter(|c| *c != usize::MAX),
                    _ => {
                        let father = self
                            .path_graph
                            .discriminants
                            .get(&self.values[value_idx].local)?;
                        self.constants
                            .get(father)
                            .copied()
                            .filter(|c| *c != usize::MAX)
                    }
                }
            }
            Constant(c) => {
                // Preserve existing behavior: if evaluation fails, we still treat this as
                // a deterministic switch and default to `0`.
                let tcx = self.tcx();
                let ty_env = TypingEnv::post_analysis(tcx, self.def_id());
                Some(
                    c.const_
                        .try_eval_target_usize(tcx, ty_env)
                        .map_or(0, |v| v as usize),
                )
            }
        }
    }

    fn switch_constraint_id_for_split(
        &mut self,
        discr: &rustc_middle::mir::Operand<'tcx>,
    ) -> Option<usize> {
        match discr {
            Copy(p) | Move(p) => {
                let value_idx = self.projection(*p);
                let tcx = self.tcx();
                let local_decls = &tcx.optimized_mir(self.def_id()).local_decls;
                let place_ty = (*p).ty(local_decls, tcx);
                match place_ty.ty.kind() {
                    TyKind::Bool => Some(value_idx),
                    _ => {
                        let father = self
                            .path_graph
                            .discriminants
                            .get(&self.values[value_idx].local)?;
                        (self.values[value_idx].local == value_idx).then_some(*father)
                    }
                }
            }
            Constant(_) => None,
        }
    }

    fn analyze_switch_successors(&mut self, bb_idx: usize) -> SwitchSuccessorPlan {
        let Some(terminator) = self.terminator(bb_idx).cloned() else {
            return SwitchSuccessorPlan::NotSwitch;
        };
        let TerminatorKind::SwitchInt { discr, targets } = terminator.kind else {
            return SwitchSuccessorPlan::NotSwitch;
        };

        if let Some(discriminant_value) = self.known_switch_value(&discr) {
            return SwitchSuccessorPlan::SingleTarget {
                target: self.switch_target_for_value(&targets, discriminant_value),
            };
        }

        let Some(constraint_id) = self.switch_constraint_id_for_split(&discr) else {
            return SwitchSuccessorPlan::NotSwitch;
        };

        let otherwise_value = self.unique_otherwise_switch_value(&discr, &targets);
        SwitchSuccessorPlan::SplitTargets {
            constraint_id,
            targets,
            otherwise_value,
        }
    }

    fn dispatch_split_switch_targets(
        &mut self,
        constraint_id: usize,
        targets: &rustc_middle::mir::SwitchTargets,
        otherwise_value: Option<usize>,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        if let Some(values) = self.possible_switch_values_for_constraint_id(constraint_id) {
            // Enumerate each possible value explicitly (bool: 0/1, enum: 0..N).
            for constraint_value in values {
                if self.visit_times() > VISIT_LIMIT {
                    continue;
                }
                let next = self.switch_target_for_value(targets, constraint_value);
                self.split_check_with_cond(
                    next,
                    constraint_id,
                    constraint_value,
                    fn_map,
                    recursion_set,
                );
            }
            return;
        }

        // Fallback: explore explicit branches + otherwise.
        for (constraint_value, branch) in targets.iter() {
            if self.visit_times() > VISIT_LIMIT {
                continue;
            }
            self.split_check_with_cond(
                branch.as_usize(),
                constraint_id,
                constraint_value as usize,
                fn_map,
                recursion_set,
            );
        }

        // `usize::MAX` is the sentinel for "otherwise/default branch" when no unique concrete
        // value can represent that arm.
        self.split_check_with_cond(
            targets.otherwise().as_usize(),
            constraint_id,
            otherwise_value.unwrap_or(usize::MAX),
            fn_map,
            recursion_set,
        );
    }

    fn dispatch_normal_successors(
        &mut self,
        successors: impl IntoIterator<Item = usize>,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        for next in successors {
            if self.visit_times() > VISIT_LIMIT {
                continue;
            }
            self.split_check(next, fn_map, recursion_set);
        }
    }

    pub fn split_check(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let snapshot = self.snapshot_state();
        self.check(bb_idx, fn_map, recursion_set);
        self.restore_state(&snapshot);
    }
    pub fn split_check_with_cond(
        &mut self,
        bb_idx: usize,
        path_discr_id: usize,
        path_discr_val: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let snapshot = self.snapshot_state();
        // Add control-sensitive indicator to the path status.
        self.constants.insert(path_discr_id, path_discr_val);
        self.check(bb_idx, fn_map, recursion_set);
        self.restore_state(&snapshot);
    }

    // the core function of the alias analysis algorithm.
    pub fn check(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let Some(_guard) = enter_depth_limit(&CHECK_DEPTH, CHECK_STACK_LIMIT) else {
            return;
        };
        self.increment_visit_times();
        if self.visit_times() > VISIT_LIMIT {
            return;
        }

        let scc_info = self.cfg_block(bb_idx).scc.clone();
        let is_scc = bb_idx == scc_info.enter && !scc_info.nodes.is_empty();

        if is_scc {
            let scc = self.sort_scc_tree(&scc_info);
            let inherited_constraints = self.constants.clone();
            let paths = self.find_scc_paths(bb_idx, &scc, &FxHashMap::default());
            rap_info!("[MoP] scc at bb{}: {} paths", bb_idx, paths.len());

            let snapshot = self.snapshot_state();
            let backup_recursion_set = recursion_set.clone();

            for path in &paths {
                if !self.is_path_reachable(&path.blocks, &inherited_constraints) {
                    continue;
                }
                rap_debug!("[MoP] path blocks: {:?}, exits: {:?}", path.blocks, path.exit_successors);
                self.restore_state(&snapshot);
                *recursion_set = backup_recursion_set.clone();

                for idx in &path.blocks {
                    self.alias_bb(*idx);
                    self.alias_bbcall(*idx, fn_map, recursion_set);
                }

                for &next in &path.exit_successors {
                    for (k, v) in path.constraints.iter() {
                        self.constants.entry(*k).or_insert(*v);
                    }
                    self.split_check(next, fn_map, recursion_set);
                }
            }
        } else {
            self.alias_bb(bb_idx);
            self.alias_bbcall(bb_idx, fn_map, recursion_set);

            let cur_next = self.cfg_block(bb_idx).next.clone();
            if cur_next.is_empty() {
                self.merge_results();
                return;
            }

            self.follow_cfg_successors(bb_idx, fn_map, recursion_set);
        }
    }

    fn follow_cfg_successors(
        &mut self,
        bb_idx: usize,
        fn_map: &mut MopFnAliasMap,
        recursion_set: &mut HashSet<DefId>,
    ) {
        let successors = self.cfg_block(bb_idx).next.clone();

        match self.analyze_switch_successors(bb_idx) {
            SwitchSuccessorPlan::SingleTarget { target } => {
                self.check(target, fn_map, recursion_set);
            }
            SwitchSuccessorPlan::SplitTargets {
                constraint_id,
                targets,
                otherwise_value,
            } => {
                self.dispatch_split_switch_targets(
                    constraint_id,
                    &targets,
                    otherwise_value,
                    fn_map,
                    recursion_set,
                );
            }
            SwitchSuccessorPlan::NotSwitch => {
                self.dispatch_normal_successors(successors, fn_map, recursion_set);
            }
        }
    }

    pub fn find_scc_paths(
        &mut self,
        start: usize,
        scc: &SccInfo,
        initial_constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccEnumeratedPath> {
        self.path_graph
            .find_scc_paths(start, scc, initial_constraints)
    }
}
