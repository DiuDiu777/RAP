mod build_stmt;
mod safety;

use super::lifetime::{RegionGraph, Rid};
use super::pattern::PatternProvider;
use crate::analysis::core::alias_analysis::AAResultMap;
use crate::analysis::testgen::context::{Context, UseKind, Var, VarState, DUMMY_UNIT_VAR};
use crate::analysis::testgen::generator::ltgen::lifetime::visit_ty_region_with;
use crate::rap_debug;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::{self, ParamEnv, Ty, TyCtxt, TypingMode};
use rustc_trait_selection::infer::InferCtxtExt;
use std::collections::{HashMap, HashSet};

pub struct LtContext<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    cx: Context<'tcx>,
    var_rid: HashMap<Var, Rid>,
    region_graph: RegionGraph,
    pat_provider: PatternProvider<'tcx>,
    alias_map: &'a AAResultMap,
    covered_api: HashSet<DefId>,
    explicit_droped_cnt: usize,
    lack_of_alias: Vec<DefId>,
}

impl<'tcx, 'a> LtContext<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, alias_map: &'a AAResultMap) -> Self {
        Self {
            tcx,
            cx: Context::new(tcx),
            var_rid: HashMap::new(),
            region_graph: RegionGraph::new(),
            pat_provider: PatternProvider::new(tcx),
            alias_map,
            covered_api: HashSet::new(),
            explicit_droped_cnt: 0,
            lack_of_alias: Vec::new(),
        }
    }

    pub fn cx(&self) -> &Context<'tcx> {
        &self.cx
    }

    pub fn into_cx(self) -> Context<'tcx> {
        self.cx
    }

    pub fn region_graph(&self) -> &RegionGraph {
        &self.region_graph
    }

    pub fn rid_of(&self, var: Var) -> Rid {
        self.var_rid[&var]
    }

    pub fn region_of(&self, var: Var) -> ty::Region<'tcx> {
        ty::Region::new_var(self.tcx, ty::RegionVid::from_usize(self.rid_of(var).into()))
    }

    pub fn dropped_count(&self) -> usize {
        self.explicit_droped_cnt
    }

    fn mk_var(&mut self, ty: Ty<'tcx>, is_input: bool) -> Var {
        if ty.is_unit() {
            return DUMMY_UNIT_VAR;
        }

        let ty = self.region_graph.register_ty(ty, self.tcx);
        let next_var = self.cx.mk_var(ty, is_input);
        let rid = self.region_graph.register_var(next_var);
        rap_debug!(
            "[mk_var] register ['?{}] {}: {:?}",
            rid.index(),
            next_var,
            ty
        );

        self.var_rid.insert(next_var, rid);

        // add structural constraint between 'var and 'a where carry by the type of var
        visit_ty_region_with(
            ty,
            Some(self.region_of(next_var)),
            self.tcx,
            &mut |from, to| {
                self.region_graph.add_edge_by_region(from, to);
            },
        );
        next_var
    }

    pub fn try_use_all_available_vars(&mut self) {
        let vars: Vec<Var> = self.cx.available_vars().collect();
        let debug_def_id = self
            .tcx
            .get_diagnostic_item(rustc_span::sym::Debug)
            .unwrap();
        let infcx = self.tcx.infer_ctxt().build(TypingMode::PostAnalysis);
        let param_env = ParamEnv::empty();

        for var in vars {
            let ty = self.cx.type_of(var);
            if self.cx.var_state(var) != VarState::BorrowedMut
                && ty != self.tcx.types.unit
                && infcx
                    .type_implements_trait(debug_def_id, [ty], param_env)
                    .must_apply_modulo_regions()
            {
                self.add_exploit_stmt(var, UseKind::Debug);
            }
        }
    }

    pub fn num_covered_api(&self) -> usize {
        self.covered_api.len()
    }
}
