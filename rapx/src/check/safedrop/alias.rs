use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty::{self},
};

use super::graph::*;
use crate::analysis::alias_analysis::default::{
    MopFnAliasMap, alias::is_no_alias_intrinsic,
};

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn alias_bb(&mut self, bb_index: usize) {
        for constant in self.alias_graph.block_facts[bb_index].const_value.clone() {
            self.alias_graph
                .constants
                .insert(constant.local, constant.value);
        }
        let block_facts = self.alias_graph.block_facts[bb_index].clone();
        for assign in block_facts.assignments {
            let lv_idx = self.alias_graph.projection(assign.lv);
            let rv_idx = self.alias_graph.projection(assign.rv);
            self.sync_drop_record();
            self.uaf_check(rv_idx, bb_index, assign.span, false);
            self.alias_graph.assign_alias(lv_idx, rv_idx);
            self.sync_drop_record();
            self.clear_drop_info(lv_idx);

            rap_debug!("Alias sets: {:?}", self.alias_graph.alias_sets.clone());
        }
    }

    pub fn alias_bbcall(&mut self, bb_index: usize, fn_map: &MopFnAliasMap) {
        if let Some(terminator) = self.alias_graph.terminator(bb_index).cloned() {
            if let TerminatorKind::Call {
                func: Operand::Constant(ref constant),
                ref args,
                ref destination,
                target: _,
                unwind: _,
                call_source: _,
                fn_span: _,
            } = terminator.kind
            {
                rap_debug!("alias_bbcall in {:?}: {:?}", bb_index, terminator);
                let lv = self.alias_graph.projection(destination.clone());
                self.sync_drop_record();
                let mut merge_vec = Vec::new();
                merge_vec.push(lv);
                let mut may_drop_flag = 0;
                if self.alias_graph.values[lv].may_drop {
                    may_drop_flag += 1;
                }
                for arg in args {
                    match arg.node {
                        Operand::Copy(ref p) | Operand::Move(ref p) => {
                            let rv = self.alias_graph.projection(p.clone());
                            self.sync_drop_record();
                            self.uaf_check(rv, bb_index, terminator.source_info.span, true);
                            merge_vec.push(rv);
                            if self.alias_graph.values[rv].may_drop {
                                may_drop_flag += 1;
                            }
                        }
                        Operand::Constant(_) => {
                            merge_vec.push(0);
                        }
                        #[cfg(rapx_rustc_ge_196)]
                        Operand::RuntimeChecks(_) => {}
                    }
                }
                if let ty::FnDef(target_id, _) = constant.const_.ty().kind() {
                    if may_drop_flag > 1 {
                        if is_no_alias_intrinsic(*target_id) {
                            return;
                        }
                        if self.alias_graph.tcx().is_mir_available(*target_id) {
                            rap_debug!("fn_map: {:?}", fn_map);
                            if fn_map.contains_key(&target_id) {
                                let fn_aliases = fn_map.get(&target_id).unwrap();
                                rap_debug!("aliases of the fn: {:?}", fn_aliases);
                                if fn_aliases.aliases().is_empty() {
                                    if let Some(l_set_idx) = self.alias_graph.find_alias_set(lv) {
                                        self.alias_graph.alias_sets[l_set_idx].remove(&lv);
                                    }
                                }
                                for alias in fn_aliases.aliases().iter() {
                                    if !alias.valuable() {
                                        continue;
                                    }
                                    self.alias_graph.handle_fn_alias(alias, &merge_vec);
                                    self.sync_drop_record();
                                }
                            }
                        } else {
                            if self.alias_graph.values[lv].may_drop {
                                for rv in &merge_vec {
                                    if self.alias_graph.values[*rv].may_drop
                                        && lv != *rv
                                        && self.alias_graph.values[lv].is_ptr()
                                    {
                                        self.alias_graph.merge_alias(lv, *rv);
                                        self.sync_drop_record();
                                        self.clear_drop_info(lv);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
