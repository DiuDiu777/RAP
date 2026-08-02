use crate::analysis::alias::observer::AliasObserver;
use crate::analysis::points_to::builder;
use crate::analysis::points_to::slot::{AbstractLoc, Slot};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{AggregateKind, Operand, Rvalue, StatementKind, TerminatorKind};

use super::graph::AliasGraph;
use super::MopFnAliasMap;

impl<'tcx> AliasGraph<'tcx> {
    pub fn init_pts_graph(&mut self) {
        self.pts_graph = builder::from_body(self.tcx(), self.def_id());
    }

    pub fn alias_bb_pts(
        &mut self,
        bb_index: usize,
        _obs: &mut dyn AliasObserver,
    ) {
        let body = self.tcx().optimized_mir(self.def_id());
        let bb = &body.basic_blocks[rustc_middle::mir::BasicBlock::from(bb_index)];

        for stmt in &bb.statements {
            match &stmt.kind {
                StatementKind::Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    self.apply_rvalue_pts(place, rvalue);
                }
                _ => {}
            }
        }
    }

    fn apply_rvalue_pts(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        rvalue: &rustc_middle::mir::Rvalue<'tcx>,
    ) {
        let lv_slot = mir_place_to_slot(place);
        let lv_idx = self.pts_graph.ensure_slot(lv_slot.clone(), false, false);
        if !self.pts_graph.may_drop(lv_idx) {
            return;
        }

        match rvalue {
            Rvalue::Use(operand, ..) => match operand {
                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                    if let Some(rv_idx) = self.try_slot_with_drop(rv_place) {
                        self.pts_graph.assign_value(lv_idx, rv_idx);
                    }
                }
                _ => {}
            },
            Rvalue::Ref(_, _, rv_place)
            | Rvalue::RawPtr(_, rv_place) => {
                let rv_slot = mir_place_to_slot(rv_place);
                self.pts_graph.assign_pointee(lv_idx, AbstractLoc::Slot(rv_slot));
                if let Some(rv_idx) = self.try_slot_with_drop(rv_place) {
                    self.pts_graph.merge_equivalence(lv_idx, rv_idx);
                }
            }
            Rvalue::CopyForDeref(rv_place) => {
                let rv_slot = mir_place_to_slot(rv_place);
                self.pts_graph.assign_pointee(lv_idx, AbstractLoc::Slot(rv_slot));
            }
            Rvalue::Cast(_, operand, _) => match operand {
                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                    if let Some(rv_idx) = self.try_slot_with_drop(rv_place) {
                        self.pts_graph.assign_value(lv_idx, rv_idx);
                    }
                }
                _ => {}
            },
            Rvalue::Aggregate(kind, operands) => {
                match kind.as_ref() {
                    AggregateKind::Tuple | AggregateKind::Adt(..) => {
                        for (field_idx, operand) in operands.iter_enumerated() {
                            match operand {
                                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                                    let field_slot = lv_slot.project(field_idx.as_usize());
                                    let field_idx_pts = self.pts_graph.ensure_slot(field_slot, false, false);
                                    if let Some(rv_idx) = self.try_slot_with_drop(rv_place) {
                                        self.pts_graph.assign_value(field_idx_pts, rv_idx);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {
                        for operand in operands {
                            match operand {
                                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                                    if let Some(rv_idx) = self.try_slot_with_drop(rv_place) {
                                        self.pts_graph.assign_value(lv_idx, rv_idx);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
            #[cfg(not(rapx_rustc_ge_196))]
            Rvalue::ShallowInitBox(operand, _) => match operand {
                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                    if let Some(rv_idx) = self.try_slot_with_drop(rv_place) {
                        self.pts_graph.assign_value(lv_idx, rv_idx);
                    }
                }
                _ => {}
            },
            Rvalue::Discriminant(rv_place) => {
                if let Some(rv_idx) = self.try_slot_with_drop(rv_place) {
                    self.pts_graph.assign_value(lv_idx, rv_idx);
                }
            }
            _ => {}
        }
    }

    fn try_slot_with_drop(&mut self, place: &rustc_middle::mir::Place<'tcx>) -> Option<usize> {
        let slot = mir_place_to_slot(place);
        let idx = self.pts_graph.ensure_slot(slot, false, false);
        if self.pts_graph.may_drop(idx) {
            Some(idx)
        } else {
            None
        }
    }

    pub fn alias_bbcall_pts(
        &mut self,
        bb_index: usize,
        fn_map: &MopFnAliasMap,
        _obs: &mut dyn AliasObserver,
    ) {
        // Build slot-index based merge_vec directly, avoiding the
        // local-index/slot-index confusion in parse_call_terminator.
        let terminator = match self.terminator(bb_index) {
            Some(t) => t.clone(),
            None => return,
        };
        let TerminatorKind::Call {
            func: ref func_op, ref args, ref destination, ..
        } = terminator.kind else { return; };
        let target_id = match func_op {
            Operand::Constant(c) => match c.ty().kind() {
                rustc_middle::ty::FnDef(id, _) => Some(*id),
                _ => None,
            },
            _ => None,
        };

        let ret_local = destination.local.as_usize();
        let ret_slot = Slot::new(ret_local);
        let ret_slot_idx = self.pts_graph.ensure_slot(ret_slot, false, false);
        if !self.pts_graph.may_drop(ret_slot_idx) {
            return;
        }

        let mut slot_args: Vec<usize> = vec![ret_slot_idx];
        let mut may_drop_count: usize = if self.pts_graph.may_drop(ret_slot_idx) { 1 } else { 0 };
        for arg in args {
            match arg.node {
                Operand::Copy(ref p) | Operand::Move(ref p) => {
                    let arg_local = p.local.as_usize();
                    let arg_slot = Slot::new(arg_local);
                    let arg_slot_idx = self.pts_graph.ensure_slot(arg_slot, false, false);
                    if self.pts_graph.may_drop(arg_slot_idx) {
                        may_drop_count += 1;
                    }
                    slot_args.push(arg_slot_idx);
                }
                Operand::Constant(_) => {
                    slot_args.push(0);
                }
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => {}
            }
        }
        if may_drop_count <= 1 {
            return;
        }

        match target_id {
            Some(id) => {
                if crate::analysis::alias::default::alias::is_no_alias_intrinsic(id) {
                    return;
                }
                if !self.tcx().is_mir_available(id) {
                    if self.ret_is_ptr(ret_local) {
                        self.pts_graph.conservative_call_merge(&slot_args);
                    }
                    return;
                }
                self.apply_fn_alias_results_pts(id, &slot_args, fn_map);
            }
            None => {
                if self.ret_is_ptr(ret_local) {
                    self.pts_graph.conservative_call_merge(&slot_args);
                }
            }
        }
    }

    fn ret_is_ptr(&self, ret_local: usize) -> bool {
        ret_local < self.values.len() && self.values[ret_local].is_ptr()
    }

    fn apply_fn_alias_results_pts(
        &mut self,
        target_id: DefId,
        merge_vec: &[usize],
        fn_map: &MopFnAliasMap,
    ) {
        let Some(fn_aliases) = fn_map.get(&target_id) else { return };
        if fn_aliases.aliases().is_empty() { return; }
        let unified: crate::analysis::alias::FnAliasPairs = From::from(fn_aliases.clone());
        self.pts_graph.apply_callee_summary(&unified, merge_vec);
    }

    pub fn merge_results_pts(&mut self) {
        let pairs = self.pts_graph.fn_alias_pairs(self.arg_size());
        for alias in pairs.aliases() {
            let lv_local = alias.left_local();
            let rv_local = alias.right_local();
            let lv_slot = self.value_to_slot_idx(lv_local).unwrap_or(lv_local);
            let rv_slot = self.value_to_slot_idx(rv_local).unwrap_or(rv_local);
            let mut mop_alias = super::MopAliasPair::new(
                alias.left_local(),
                self.pts_graph.may_drop(lv_slot),
                self.pts_graph.need_drop(lv_slot),
                alias.right_local(),
                self.pts_graph.may_drop(rv_slot),
                self.pts_graph.need_drop(rv_slot),
            );
            mop_alias.fact = alias.clone();
            self.ret_alias.add_alias(mop_alias);
        }
    }
}

fn mir_place_to_slot(place: &rustc_middle::mir::Place) -> Slot {
    let local = place.local.as_usize();
    let fields: Vec<usize> = place
        .projection
        .iter()
        .filter_map(|elem| match elem {
            rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
            _ => None,
        })
        .collect();
    Slot { local, fields }
}
