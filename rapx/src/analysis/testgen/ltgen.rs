mod select;

use super::context_builder::ContextBuilder;
use crate::analysis::core::alias_analysis::AAResultMap;
use crate::analysis::core::api_dependency::{graph::TransformKind, ApiDependencyGraph, DepNode};
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

pub struct LtGen<'tcx, 'a, R: Rng> {
    tcx: TyCtxt<'tcx>,
    rng: RefCell<R>,
    max_complexity: usize,
    max_iteration: usize,
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
        LtGen {
            pub_api: utils::get_all_pub_apis(tcx),
            tcx,
            rng: RefCell::new(rng),
            max_complexity,
            max_iteration,
            alias_map,
            api_graph,
            covered_api: HashSet::new(),
            reached_map: HashMap::new(),
        }
    }

    fn weight_of_nodes(&self, nodes: &[DepNode<'tcx>]) -> Vec<f32> {
        nodes
            .iter()
            .map(|node| {
                let num_of_reach = *self.reached_map.get(node).unwrap_or(&0);
                1.0 / (1 + num_of_reach) as f32
            })
            .collect()
    }

    fn eligable_nodes(&self, cx: &ContextBuilder<'tcx, 'a>) -> Vec<DepNode<'tcx>> {
        let tys: Vec<_> = cx
            .available_vars()
            .into_iter()
            .map(|var| cx.cx().type_of(var))
            .collect();

        rap_debug!(
            "live tys: {}",
            tys.iter().map(|ty| format!("{ty}")).join(", ")
        );

        self.api_graph.eligible_nodes_with(&tys)
    }

    fn next(&mut self, cx: &mut ContextBuilder<'tcx, 'a>) -> Option<DepNode<'tcx>> {
        rap_debug!(
            "live vars: {}",
            cx.available_vars()
                .map(|var| format!("{var}: {:?}", cx.cx().type_of(var)))
                .join(", ")
        );

        rap_debug!(
            "varstate: {}",
            cx.cx()
                .vars()
                .map(|var| { format!("{} -> {}", var, cx.var_state(var)) })
                .join(", ")
        );

        rap_debug!("live state: {:?}", cx.live_state());

        let nodes = self.eligable_nodes(cx);
        rap_debug!("# eligible actions = {}", nodes.len());
        rap_debug!("eligible actions: {:?}", nodes);

        // No action can do
        if nodes.is_empty() {
            return None;
        }

        let weights = if !utils::is_env_var_exist("TESTGEN_DISABLE_WEIGHT") {
            self.weight_of_nodes(&nodes)
        } else {
            vec![1.0f32; nodes.len()]
        };

        let dist = WeightedIndex::new(&weights).unwrap();
        rap_debug!(
            "weights: {}",
            nodes
                .iter()
                .zip(weights.iter())
                .map(|(node, weight)| { format!("{:?}: {:.2}", node, weight) })
                .collect::<Vec<_>>()
                .join(", ")
        );
        let index = self.rng.borrow_mut().sample(dist);
        *self.reached_map.entry(nodes[index].clone()).or_default() += 1;
        Some(nodes[index])
    }

    // pub fn print_brief()

    pub fn cx_complexity(&self, cx: &ContextBuilder<'tcx, 'a>) -> usize {
        cx.cx().num_apicall()
    }

    pub fn gen(&mut self) -> ContextBuilder<'tcx, 'a> {
        let mut builder = ContextBuilder::new(self.tcx, &self.alias_map);
        let (estimated, total) = self.api_graph.estimate_coverage();
        let mut count = 0;
        let mut num_drop_inject = 0;
        loop {
            count += 1;
            if count > self.max_iteration {
                rap_info!("max iteration reached, generation terminate");
                break;
            }
            rap_info!("<<<<< Iter {} >>>>>", count);
            if self.cx_complexity(&builder) > self.max_complexity {
                rap_info!("complexity limit reached, generation terminate");
                break;
            }

            if let Some(action) = self.next(&mut builder) {
                builder.comment_current_state();
                match action {
                    DepNode::Api(fn_did, args) => {
                        rap_debug!(
                            "[next] select API call: {}",
                            self.tcx.def_path_str_with_args(fn_did, args)
                        );

                        if let Some(call) = self.get_eligable_call(fn_did, args, &mut builder) {
                            self.covered_api.insert(call.fn_did());
                            builder.add_call_stmt(call);
                            if self.rng.borrow_mut().random_ratio(1, 2)
                                && builder.try_inject_drop()
                                && !utils::is_env_var_exist("TESTGEN_DISABLE_INJECT")
                            {
                                num_drop_inject += 1;
                                rap_debug!("successfully inject drop");
                            }
                        }
                    }
                    DepNode::Ty(ty) => {
                        let transforms = self.api_graph.eligible_transforms_to(ty.ty());
                        rap_debug!("ty = {}", ty.ty());
                        rap_debug!(
                            "transforms = {}",
                            transforms
                                .iter()
                                .map(|(ty, kind)| format!("{} -> {}", ty.ty(), kind))
                                .collect::<Vec<_>>()
                                .join(", ")
                        );

                        let mut var_transforms = Vec::new();
                        for var in builder.available_vars() {
                            for (ty, kind) in transforms.iter() {
                                if utils::is_ty_eq(builder.cx().type_of(var), ty.ty(), self.tcx) {
                                    var_transforms.push((var, *kind));
                                }
                            }
                        }

                        rap_debug!("[next] transforms: {var_transforms:?}");

                        let (var, kind) =
                            var_transforms.choose(self.rng.get_mut()).unwrap().clone();

                        rap_debug!(
                            "[next] select transform: {}: {} {}",
                            var,
                            builder.cx().type_of(var),
                            kind
                        );
                        match kind {
                            TransformKind::Ref(mutability) => {
                                builder.add_ref_stmt(var, mutability, None);
                            }
                            _ => {
                                panic!("not implemented yet");
                            }
                        }
                    }
                }
            } else {
                rap_info!("no eligable action, generation terminate");
                break;
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
