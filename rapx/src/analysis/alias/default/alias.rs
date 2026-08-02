use super::{MopFnAliasMap, graph::*};
use crate::analysis::alias::observer::AliasObserver;
use crate::analysis::alias::default::types::ValueKind;
use crate::def_id::*;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{AggregateKind, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind},
    ty::{self, TyCtxt},
};
use rustc_span::Span;
use std::collections::HashSet;

const MAX_VALUES_PER_PATH: usize = 1000;

impl<'tcx> AliasGraph<'tcx> {
    // ── Unified BB processing (used by both MoP and SafeDrop) ──────

    pub fn alias_bb(&mut self, bb_index: usize, obs: &mut dyn AliasObserver) {
        let body = self.tcx().optimized_mir(self.def_id());
        let bb = &body.basic_blocks[rustc_middle::mir::BasicBlock::from(bb_index)];

        for stmt in &bb.statements {
            let span = stmt.source_info.span;
            match &stmt.kind {
                StatementKind::Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    self.process_assign_bb(place, rvalue, span, obs);
                }
                _ => {}
            }
        }
    }

    fn process_assign_bb(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        span: Span,
        obs: &mut dyn AliasObserver,
    ) {
        let lv_local = place.local.as_usize();
        if lv_local >= self.values.len() || !self.values[lv_local].may_drop {
            return;
        }

        match rvalue {
            Rvalue::Use(operand, ..) => match operand {
                Operand::Copy(rv_place) => {
                    let rv_local = rv_place.local.as_usize();
                    if rv_local < self.values.len() && self.values[rv_local].may_drop {
                        let lv_idx = self.projection(*place);
                        let rv_idx = self.projection(*rv_place);
                        obs.on_value_use(self, rv_idx, span, false);
                        self.pts_assign_value(lv_idx, rv_idx);
                        obs.on_value_assign(self, lv_idx);
                    }
                }
                Operand::Move(rv_place) => {
                    let rv_local = rv_place.local.as_usize();
                    if rv_local < self.values.len() && self.values[rv_local].may_drop {
                        let lv_idx = self.projection(*place);
                        let rv_idx = self.projection(*rv_place);
                        self.move_sources.insert(lv_idx, rv_idx);
                        obs.on_value_use(self, rv_idx, span, false);
                        if self.values[rv_idx].kind == ValueKind::RawPtr {
                            self.pts_assign_value(lv_idx, rv_idx);
                        }
                        obs.on_value_assign(self, lv_idx);
                    }
                }
                Operand::Constant(_c) => {}
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => {}
            },
            Rvalue::Ref(_, _, rv_place)
            | Rvalue::RawPtr(_, rv_place)
            | Rvalue::CopyForDeref(rv_place) => {
                let rv_local = rv_place.local.as_usize();
                if rv_local < self.values.len() && self.values[rv_local].may_drop {
                    let lv_idx = self.projection(*place);
                    let rv_idx = self.projection(*rv_place);
                    obs.on_value_use(self, rv_idx, span, false);
                    self.pts_assign_pointee(lv_idx, rv_idx);
                    obs.on_value_assign(self, lv_idx);
                }
            }
            Rvalue::Cast(_, operand, _) => match operand {
                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                    let rv_local = rv_place.local.as_usize();
                    if rv_local < self.values.len() && self.values[rv_local].may_drop {
                        let lv_idx = self.projection(*place);
                        let rv_idx = self.projection(*rv_place);
                        obs.on_value_use(self, rv_idx, span, false);
                        self.pts_assign_value(lv_idx, rv_idx);
                        obs.on_value_assign(self, lv_idx);
                    }
                }
                _ => {}
            },
            Rvalue::Aggregate(kind, operands) => {
                match kind.as_ref() {
                    AggregateKind::Tuple | AggregateKind::Adt(..) => {
                        let body = self.tcx().optimized_mir(self.def_id());
                        let lv_ty = place.ty(&body.local_decls, self.tcx()).ty;
                        for (field_idx, operand) in operands.iter_enumerated() {
                            match operand {
                                Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                                    let rv_local = rv_place.local.as_usize();
                                    if rv_local < self.values.len() && self.values[rv_local].may_drop {
                                        let field_ty = resolve_field_ty(lv_ty, field_idx.as_usize(), self.tcx());
                                        if let Some(ft) = field_ty {
                                            let lv_field = self.tcx().mk_place_field(*place, field_idx, ft);
                                            let lv_idx = self.projection(lv_field);
                                            let rv_idx = self.projection(*rv_place);
                                            obs.on_value_use(self, rv_idx, span, false);
                                            self.pts_assign_value(lv_idx, rv_idx);
                                            obs.on_value_assign(self, lv_idx);
                                        }
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
                                    let rv_local = rv_place.local.as_usize();
                                    if rv_local < self.values.len() && self.values[rv_local].may_drop {
                                        let lv_idx = self.projection(*place);
                                        let rv_idx = self.projection(*rv_place);
                                        obs.on_value_use(self, rv_idx, span, false);
                                        self.pts_assign_value(lv_idx, rv_idx);
                                        obs.on_value_assign(self, lv_idx);
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
                    let rv_local = rv_place.local.as_usize();
                    if rv_local < self.values.len() && self.values[rv_local].may_drop {
                        let lv_idx = self.projection(*place);
                        let rv_idx = self.projection(*rv_place);
                        obs.on_value_use(self, rv_idx, span, false);
                        self.pts_assign_value(lv_idx, rv_idx);
                        obs.on_value_assign(self, lv_idx);
                    }
                }
                _ => {}
            },
            Rvalue::Discriminant(rv_place) => {
                let rv_local = rv_place.local.as_usize();
                if rv_local < self.values.len() && self.values[rv_local].may_drop {
                    let lv_idx = self.projection(*place);
                    let rv_idx = self.projection(*rv_place);
                    obs.on_value_use(self, rv_idx, span, false);
                    self.pts_assign_value(lv_idx, rv_idx);
                    obs.on_value_assign(self, lv_idx);
                }
            }
            _ => {}
        }
    }

    // ── Unified call processing ──

    pub fn alias_bbcall(
        &mut self,
        bb_index: usize,
        fn_map: &MopFnAliasMap,
        obs: &mut dyn AliasObserver,
    ) {
        let Some((merge_vec, may_drop_count, target_id, span)) =
            self.parse_call_terminator(bb_index)
        else { return; };

        // Check UAF for arguments (not the return value destination,
        // which is being assigned a fresh value).
        for &vidx in merge_vec.iter().skip(1) {
            if vidx != 0 {
                obs.on_value_use(self, vidx, span, true);
            }
        }
        if may_drop_count <= 1 {
            if merge_vec[0] != 0 && self.values[merge_vec[0]].may_drop {
                if let Some(slot_idx) = self.value_to_slot_idx(merge_vec[0]) {
                    self.pts_graph.reset_partition(slot_idx);
                }
                obs.on_value_assign(self, merge_vec[0]);
            }
            return;
        }

        match target_id {
            Some(id) => {
                if is_no_alias_intrinsic(id) { return; }
                if !self.tcx().is_mir_available(id) {
                    if self.values[merge_vec[0]].may_drop {
                        self.conservative_call_merge(&merge_vec, obs);
                    }
                    return;
                }
                self.apply_fn_alias_results(id, &merge_vec, fn_map, obs);
            }
            None => {
                if self.values[merge_vec[0]].may_drop {
                    self.conservative_call_merge(&merge_vec, obs);
                }
            }
        }

        if merge_vec[0] != 0 && self.values[merge_vec[0]].may_drop {
            obs.on_value_assign(self, merge_vec[0]);
        }
    }

    fn conservative_call_merge(&mut self, merge_vec: &[usize], obs: &mut dyn AliasObserver) {
        let lv = merge_vec[0];
        for &rv in merge_vec.iter().skip(1) {
            if rv != 0 && self.values[rv].may_drop && lv != rv && self.values[lv].is_ptr() {
                let lv_s = self.value_to_slot_idx(lv).unwrap_or(lv);
                let rv_s = self.value_to_slot_idx(rv).unwrap_or(rv);
                self.pts_graph.merge_equivalence(lv_s, rv_s);
                obs.on_value_assign(self, lv);
            }
        }
    }

    fn apply_fn_alias_results(
        &mut self, target_id: DefId, merge_vec: &[usize],
        fn_map: &MopFnAliasMap, obs: &mut dyn AliasObserver,
    ) {
        let Some(fn_aliases) = fn_map.get(&target_id) else { return; };
        if fn_aliases.aliases().is_empty() { return; }
        let unified: crate::analysis::alias::FnAliasPairs = From::from(fn_aliases.clone());
        let slot_merge: Vec<usize> = merge_vec
            .iter()
            .map(|&v| self.value_to_slot_idx(v).unwrap_or(v))
            .collect();
        self.pts_graph.apply_callee_summary(&unified, &slot_merge);
        obs.on_state_change(self);
    }

    // ── PtsGraph value-flow operations ──

    fn pts_assign_value(&mut self, lv_idx: usize, rv_idx: usize) {
        let lv = self.value_to_slot_idx(lv_idx).unwrap_or(lv_idx);
        let rv = self.value_to_slot_idx(rv_idx).unwrap_or(rv_idx);
        self.pts_graph.assign_value(lv, rv);
    }

    fn pts_assign_pointee(&mut self, lv_idx: usize, rv_idx: usize) {
        use crate::analysis::points_to::slot::{AbstractLoc, Slot};
        let lv = self.value_to_slot_idx(lv_idx).unwrap_or(lv_idx);
        let slot = Slot {
            local: self.values[rv_idx].local,
            fields: self.get_field_seq(rv_idx).into_iter().rev().collect(),
        };
        self.pts_graph.assign_pointee(lv, AbstractLoc::Slot(slot));
        let rv = self.value_to_slot_idx(rv_idx).unwrap_or(rv_idx);
        self.pts_graph.merge_equivalence(lv, rv);
    }

    // ── Place projection (for SafeDrop compatibility) ──

    pub fn projection(&mut self, place: rustc_middle::mir::Place<'tcx>) -> usize {
        let local = place.local.as_usize();
        let mut value_idx = local;
        for proj in place.projection {
            match proj {
                ProjectionElem::Deref => {}
                ProjectionElem::Field(field, ty) => {
                    let field_idx = field.as_usize();
                    if !self.values[value_idx].fields.contains_key(&field_idx) {
                        if self.values.len() < MAX_VALUES_PER_PATH {
                            let ty_env = ty::TypingEnv::post_analysis(self.tcx(), self.def_id());
                            let need_drop = ty.needs_drop(self.tcx(), ty_env);
                            let may_drop = !super::types::is_not_drop(self.tcx(), ty);
                            let mut node = super::value::Value::new(
                                self.values.len(), local,
                                need_drop, need_drop || may_drop,
                            );
                            node.kind = super::types::kind(ty);
                            node.father = Some(super::value::FatherInfo::new(value_idx, field_idx));
                            let node_index = node.index;
                            self.values[value_idx].fields.insert(field_idx, node.index);
                            self.values.push(node);
                            // Sync with PtsGraph
                            let field_slot = crate::analysis::points_to::slot::Slot {
                                local,
                                fields: self.get_field_seq(node_index).into_iter().rev().collect(),
                            };
                            self.pts_graph.ensure_slot(field_slot, may_drop, need_drop);
                        } else { break; }
                    }
                    value_idx = *self.values[value_idx].fields.get(&field_idx).unwrap();
                }
                _ => {}
            }
        }
        value_idx
    }

    // ── Inter-proc helpers ──

    pub fn call_target_of(&self, bb_index: usize) -> Option<DefId> {
        let term = self.terminator(bb_index)?;
        match &term.kind {
            TerminatorKind::Call { func: Operand::Constant(c), .. } => match c.ty().kind() {
                ty::FnDef(id, _) => Some(*id),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn parse_call_terminator(
        &mut self, bb_index: usize,
    ) -> Option<(Vec<usize>, usize, Option<DefId>, Span)> {
        let terminator = self.terminator(bb_index)?.clone();
        let TerminatorKind::Call {
            func: Operand::Constant(ref constant),
            ref args, ref destination, ..
        } = terminator.kind else { return None; };
        let span = terminator.source_info.span;
        let lv = destination.local.as_usize();
        let mut merge_vec = vec![lv];
        let mut may_drop_count = if self.values[lv].may_drop { 1 } else { 0 };
        for arg in args {
            match arg.node {
                Operand::Copy(ref p) | Operand::Move(ref p) => {
                    let rv = p.local.as_usize();
                    merge_vec.push(rv);
                    if self.values[rv].may_drop { may_drop_count += 1; }
                }
                Operand::Constant(_) => { merge_vec.push(0); }
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => {}
            }
        }
        let target_id = match constant.const_.ty().kind() {
            ty::FnDef(id, _) => Some(*id),
            _ => None,
        };
        Some((merge_vec, may_drop_count, target_id, span))
    }

    fn get_field_seq(&self, value_idx: usize) -> Vec<usize> {
        let mut seq = vec![];
        let mut cur = value_idx;
        let mut iter = 0usize;
        while let Some(ref father) = self.values[cur].father {
            iter += 1;
            if iter > 1000 { break; }
            seq.push(father.field_id);
            cur = father.father_value_id;
        }
        seq
    }
}

// ── Standalone helpers ──

pub fn is_no_alias_intrinsic(def_id: DefId) -> bool {
    let v = [call_mut_opt(), clone_opt(), take_opt(), replace_opt()];
    contains(&v, def_id)
}

pub fn ensure_fn_aliases_cached<'tcx>(
    tcx: TyCtxt<'tcx>,
    target_id: DefId,
    fn_map: &mut MopFnAliasMap,
    recursion_set: &mut HashSet<DefId>,
) {
    if fn_map.contains_key(&target_id) || recursion_set.contains(&target_id) {
        return;
    }
    if !tcx.is_mir_available(target_id) {
        return;
    }
    recursion_set.insert(target_id);
    let mut alias_graph = AliasGraph::new(tcx, target_id);
    alias_graph.path_graph.find_scc();
    alias_graph.process_function_paths(fn_map, recursion_set);
    let ret_alias = alias_graph.ret_alias.clone();
    rap_debug!("Find aliases of {:?}: {:?}", target_id, ret_alias);
    fn_map.insert(target_id, ret_alias);
    recursion_set.remove(&target_id);
}

fn resolve_field_ty<'tcx>(
    lv_ty: rustc_middle::ty::Ty<'tcx>,
    field_idx: usize,
    _tcx: TyCtxt<'tcx>,
) -> Option<rustc_middle::ty::Ty<'tcx>> {
    match lv_ty.kind() {
        ty::TyKind::Tuple(fields) => fields.get(field_idx).copied(),
        ty::TyKind::Adt(adt_def, _substs) => {
            adt_def.all_fields().nth(field_idx).map(|_f| lv_ty)
        }
        _ => None,
    }
}
