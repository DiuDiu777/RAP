mod select;

use super::context_builder::ContextBuilder;
use crate::analysis::core::alias_analysis::AAResultMap;
use crate::analysis::core::api_dependency::{graph::TransformKind, ApiDependencyGraph, DepNode};
use crate::analysis::testgen::context::DUMMY_INPUT_VAR;
use crate::analysis::testgen::utils::{self};
use crate::{rap_debug, rap_info};
use itertools::Itertools;
use rand::distr::weighted::WeightedIndex;
use rand::rngs::ThreadRng;
use rand::seq::IndexedRandom;
use rand::{self, Rng};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::AddAssign;

pub struct LtGenBuilder<'tcx, 'a, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: R,
    max_complexity: usize,
    max_iteration: usize,
    alias_map: &'a AAResultMap,
    api_graph: ApiDependencyGraph<'tcx>,
}

impl<'tcx, 'a> LtGenBuilder<'tcx, 'a, ThreadRng> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        alias_map: &'a AAResultMap,
        api_graph: ApiDependencyGraph<'tcx>,
    ) -> LtGenBuilder<'tcx, 'a, ThreadRng> {
        LtGenBuilder {
            tcx,
            rng: rand::rng(),
            max_complexity: 20,
            max_iteration: 1000,
            alias_map,
            api_graph: api_graph,
        }
    }
}

impl<'tcx, 'a, R: Rng> LtGenBuilder<'tcx, 'a, R> {
    pub fn build(self) -> LtGen<'tcx, 'a, R> {
        LtGen::new(
            self.tcx,
            self.alias_map,
            self.rng,
            self.max_complexity,
            self.max_iteration,
            self.api_graph,
        )
    }

    pub fn max_iteration(mut self, max_iteration: usize) -> Self {
        self.max_iteration = max_iteration;
        self
    }

    pub fn max_complexity(mut self, max_complexity: usize) -> Self {
        self.max_complexity = max_complexity;
        self
    }

    pub fn rng(mut self, rng: R) -> Self {
        self.rng = rng;
        self
    }
}

pub struct Config {
    max_complexity: usize,
    max_iteration: usize,
    num_samples: usize,
    top_k: usize,
}

pub struct LtGen<'tcx, 'a, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: RefCell<R>,
    config: Config,
    pub_api: Vec<DefId>,
    alias_map: &'a AAResultMap,
    api_graph: ApiDependencyGraph<'tcx>,
    covered_api: HashSet<DefId>,
    reached_map: HashMap<DepNode<'tcx>, usize>,
}

impl<'tcx, 'a, R: Rng> LtGen<'tcx, 'a, R> {
    fn new(
        tcx: TyCtxt<'tcx>,
        alias_map: &'a AAResultMap,
        rng: R,
        max_complexity: usize,
        max_iteration: usize,
        api_graph: ApiDependencyGraph<'tcx>,
    ) -> Self {
        let config = Config {
            max_complexity,
            max_iteration,
            num_samples: 5,
            top_k: 10,
        };
        LtGen {
            pub_api: utils::get_all_pub_apis(tcx),
            tcx,
            rng: RefCell::new(rng),
            config,
            alias_map,
            api_graph,
            covered_api: HashSet::new(),
            reached_map: HashMap::new(),
        }
    }

    fn cx_complexity(&self, builder: &ContextBuilder<'tcx, 'a>) -> usize {
        builder.cx().num_apicall()
    }

    pub fn gen(&mut self) -> ContextBuilder<'tcx, 'a> {
        let mut builder = ContextBuilder::new(self.tcx, &self.alias_map);
        let (estimated, total) = self.api_graph.estimate_coverage();
        let mut count = 0;
        let mut num_drop_inject = 0;
        loop {
            count += 1;
            rap_info!("<<<<< Iter {} >>>>>", count);

            if count > self.config.max_iteration {
                rap_info!("max iteration reached, generation terminate");
                break;
            }

            if self.cx_complexity(&builder) > self.config.max_complexity {
                rap_info!("complexity limit reached, generation terminate");
                break;
            }

            let Some(action) = self.next(&mut builder) else {
                rap_info!("no eligable action, generation terminate");
                break;
            };

            builder.comment_current_state();
            let mut call = action.call().clone();

            rap_debug!(
                "[next] select API call: {}",
                self.tcx
                    .def_path_str_with_args(call.fn_did(), self.tcx.mk_args(call.generic_args()))
            );

            // first build transform stmts for vars

            for (var, transforms) in call.args_mut().iter_mut().zip(action.transforms()) {
                rap_trace!("var = {}, transforms = {:?}", var, transforms);
                if *var == DUMMY_INPUT_VAR {
                    rap_trace!("skip DUMMY INPUT");
                    continue;
                }
                for transform in transforms {
                    match transform {
                        TransformKind::Ref(mutability) => {
                            *var = builder.add_ref_stmt(*var, *mutability, None);
                        }
                        _ => {
                            unimplemented!();
                        }
                    }
                }
            }

            self.covered_api.insert(call.fn_did());
            self.reached_map
                .entry(action.node())
                .or_default()
                .add_assign(1);
            let place = builder.add_call_stmt(call);

            // linear probability to inject drop
            let prob;
            if utils::is_env_var_exist("TESTGEN_DISABLE_INJECT") {
                prob = 0.0;
            } else {
                prob = 1f64
                    .min(self.cx_complexity(&builder) as f64 / self.config.max_complexity as f64);
            }

            if self.rng.borrow_mut().random_bool(prob) && builder.try_inject_drop() {
                num_drop_inject += 1;
                rap_info!("successfully inject drop");
            }

            // try exploit
            if builder.try_add_exploit_stmt_for(place) {
                rap_info!("add exploit stmt for {place}");
            }

            rap_info!(
                "num_stmt={}, complexity={}, num_drop_inject={}, covered/estimated/total_api={}/{}/{}",
                builder.cx().num_stmt(),
                self.cx_complexity(&builder),
                num_drop_inject,
                builder.num_covered_api(),
                estimated,
                total,
            );

            rap_info!(
                "coverage={:.3}/{:.3}/{:.3} (current/global/estimated_max)",
                builder.num_covered_api() as f32 / total as f32,
                self.covered_api.len() as f32 / total as f32,
                estimated as f32 / total as f32
            );
        }
        builder.comment_current_state();
        builder.try_add_exploit_stmts();
        builder
    }

    pub fn count_generic_api(&self) -> usize {
        self.pub_api
            .iter()
            .filter(|did| utils::fn_requires_monomorphization(**did, self.tcx))
            .count()
    }

    pub fn statistic_str(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!("# APIs = {}\n", self.pub_api.len()));
        s.push_str(&format!("# generic APIs = {}\n", self.count_generic_api()));
        s.push_str(&format!("# covered APIs = {}\n", self.covered_api.len()));
        s.push_str("covered APIs:\n");
        s.push_str(
            &self
                .covered_api
                .iter()
                .map(|did| format!("{:?}", did))
                .join(", "),
        );
        s.push_str("\nuncovered APIs:\n");
        s.push_str(
            &self
                .pub_api
                .iter()
                .filter(|did| !self.covered_api.contains(did))
                .map(|did| format!("{:?}", did))
                .join(", "),
        );

        s
    }
}
