use super::decomposition::GraphDecomposer;
use super::state::AbstractState;
use super::topology::{SccMetadata, Slice};
use crate::analysis::core::alias_analysis::default::graph::MopGraph;
use crate::analysis::utils::fn_info::get_cleaned_def_path_name;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{Operand, TerminatorKind};
use std::collections::VecDeque;
use std::time::{Duration, Instant};

/// The main analyzer struct for Hierarchical Analysis.
///
/// It orchestrates the SCC decomposition, constraint solving, and alias simulation.
pub struct HierarchicalAnalyzer<'a, 'tcx> {
    /// Mutable reference to the MopGraph (Control Flow and Data Flow Graph).
    pub graph: &'a mut MopGraph<'tcx>,

    /// The hierarchical tree of SCCs.
    pub scc_tree: Vec<SccMetadata>,

    /// Map from Dominator Node ID to its corresponding SCC Metadata.
    /// Used for fast lookup of nested SCCs during simulation.
    pub dom_to_scc: FxHashMap<usize, SccMetadata>,

    /// Cache for SCC summaries to avoid re-analyzing the same context.
    /// Format: (SCC_ID, Entry_State, List_of_Exit_States)
    pub summary_cache: Vec<(usize, AbstractState, Vec<(usize, AbstractState)>)>,

    // Performance metrics
    pub time_decomp: Duration,
    pub time_constraint: Duration,
    pub time_alias: Duration,
    pub time_path_synth: Duration,
    pub time_total: Duration,
    pub max_scc_stats: (usize, usize, usize),
}

impl<'a, 'tcx> HierarchicalAnalyzer<'a, 'tcx> {
    pub fn new(graph: &'a mut MopGraph<'tcx>) -> Self {
        HierarchicalAnalyzer {
            graph,
            scc_tree: Vec::new(),
            dom_to_scc: FxHashMap::default(),
            summary_cache: Vec::new(),
            time_decomp: Duration::new(0, 0),
            time_constraint: Duration::new(0, 0),
            time_alias: Duration::new(0, 0),
            time_path_synth: Duration::new(0, 0),
            time_total: Duration::new(0, 0),
            max_scc_stats: (0, 0, 0),
        }
    }

    /// Main entry point for the analysis.
    ///
    /// 1. Decomposes the graph into SCCs.
    /// 2. Iterates through the graph using a worklist algorithm.
    /// 3. Handles nested SCCs hierarchically using summaries.
    pub fn run_analysis(&mut self) -> FxHashMap<usize, Vec<AbstractState>> {
        // Skip formatting functions
        if get_cleaned_def_path_name(self.graph.tcx, self.graph.def_id).contains("fmt::write") {
            return FxHashMap::default();
        }

        // Decomposition Phase
        let t_decomp = Instant::now();
        let decomposer = GraphDecomposer::new(self.graph);
        let (tree, map) = decomposer.build_scc_hierarchy();
        self.scc_tree = tree;
        self.dom_to_scc = map;
        self.time_decomp += t_decomp.elapsed();

        let mut worklist: VecDeque<(usize, AbstractState)> = VecDeque::new();
        let mut block_results: FxHashMap<usize, Vec<AbstractState>> = FxHashMap::default();

        // Initialize analysis at the entry block
        worklist.push_back((0, AbstractState::new()));

        while let Some((bb_idx, state)) = worklist.pop_front() {
            // Check for convergence (fix-point)
            if self.is_covered(bb_idx, &state, &block_results) {
                continue;
            }

            // Record state for future convergence checks
            let t_alias_rec = Instant::now();
            self.record_state(bb_idx, state.clone(), &mut block_results);
            self.time_alias += t_alias_rec.elapsed();

            // Check if we are entering an SCC (Hierarchical Step)
            if let Some(scc) = self.dom_to_scc.clone().get(&bb_idx) {
                let exit_states = self.enumerate_scc(scc, state);

                // Propagate results from SCC exits
                for (target_bb, exit_state) in exit_states {
                    worklist.push_back((target_bb, exit_state));
                }
            } else {
                // Standard Basic Block Handling
                let t_alias_calc = Instant::now();

                // Restore graph state to the context of this abstract state
                state.restore_to(self.graph);

                // Perform intra-block alias analysis
                self.graph.alias_bb(bb_idx);
                let mut dummy_map = FxHashMap::default();
                let mut dummy_set = std::collections::HashSet::default();
                self.graph
                    .alias_bbcall(bb_idx, &mut dummy_map, &mut dummy_set);

                // Update path history
                let mut current_path = state.path.clone();
                if current_path.last() != Some(&bb_idx) {
                    current_path.push(bb_idx);
                }

                // If function exit, merge results
                if self.graph.blocks[bb_idx].next.is_empty() {
                    self.graph.merge_results();
                }

                let mut new_state = AbstractState::snapshot(self.graph);
                new_state.path = current_path;
                self.time_alias += t_alias_calc.elapsed();

                // Propagate to successors with constraint checks
                if let Some(block) = self.graph.blocks.clone().get(bb_idx) {
                    for &succ in &block.next {
                        new_state.restore_to(self.graph);

                        // Apply branch constraints (Discretized Constraint Propagation)
                        if self.apply_branch_constraint(bb_idx, succ) {
                            let mut next_state = AbstractState::snapshot(self.graph);
                            next_state.path = new_state.path.clone();
                            worklist.push_back((succ, next_state));
                        }
                    }
                }
            }
        }

        self.print_statistics();
        block_results
    }

    fn print_statistics(&self) {
        let time_other = self
            .time_total
            .saturating_sub(self.time_decomp)
            .saturating_sub(self.time_constraint)
            .saturating_sub(self.time_path_synth)
            .saturating_sub(self.time_alias);

        rap_debug!("1. Decomposition: {:.2?}", self.time_decomp);
        rap_debug!("2. Constraint:    {:.2?}", self.time_constraint);
        rap_debug!("3. Path Synthesis:{:.2?}", self.time_path_synth);
        rap_debug!("4. Alias Comp:    {:.2?}", self.time_alias);
        rap_debug!("5. Traversal/Misc:{:.2?}", time_other);
        rap_debug!("===========================");
    }

    /// Enumerates paths through an SCC to compute summary transfer functions.
    fn enumerate_scc(
        &mut self,
        scc: &SccMetadata,
        entry_state: AbstractState,
    ) -> Vec<(usize, AbstractState)> {
        // Check Cache first
        let t_cache = Instant::now();
        for (id, cached_entry, cached_result) in &self.summary_cache {
            if *id == scc.id {
                // Precise match requirement for caching
                if self.is_substate_of(&entry_state, cached_entry)
                    && self.is_substate_of(cached_entry, &entry_state)
                {
                    self.time_alias += t_cache.elapsed();
                    return cached_result.clone();
                }
            }
        }

        // Slice Generation (Path Synthesis)
        let t_synth = Instant::now();
        let loop_slices = self.find_loop_slices(scc);
        let exit_slices = self.find_exit_slices(scc);
        self.time_path_synth += t_synth.elapsed();

        let mut worklist = VecDeque::new();
        worklist.push_back(entry_state.clone());
        let mut history: Vec<AbstractState> = Vec::new();
        let mut final_exits = Vec::new();

        let mut max_loop_depth = 0;

        // Iterate within the SCC
        while let Some(current_state) = worklist.pop_front() {
            if !self.is_fresh(&current_state, &history) {
                continue;
            }
            history.retain(|old_state| !self.is_substate_of(old_state, &current_state));
            history.push(current_state.clone());

            if current_state.iter_count > max_loop_depth {
                max_loop_depth = current_state.iter_count;
            }

            // Simulate Loop Back-edges
            for slice in &loop_slices {
                let next_states = self.simulate_slice(&current_state, slice);
                for mut next_state in next_states {
                    next_state.iter_count += 1;
                    worklist.push_back(next_state);
                }
            }

            // Simulate Exits
            for slice in &exit_slices {
                let out_states = self.simulate_slice(&current_state, slice);
                for out_state in out_states {
                    final_exits.push((slice.end_node, out_state));
                }
            }
        }

        if max_loop_depth >= 10 {
            rap_warn!(
                ">>> Potential Non-termination in SCC {}. Depth 10 reached.",
                scc.id
            );
        }

        // Deduplicate results
        let t_dedup = Instant::now();
        let mut unique_exits: Vec<(usize, AbstractState)> = Vec::new();
        for (target, state) in final_exits {
            let mut is_redundant = false;
            for (u_target, u_state) in &unique_exits {
                if target == *u_target && self.is_substate_of(&state, u_state) {
                    is_redundant = true;
                    break;
                }
            }
            if !is_redundant {
                unique_exits.retain(|(t, s)| *t != target || !self.is_substate_of(s, &state));
                unique_exits.push((target, state));
            }
        }
        self.time_alias += t_dedup.elapsed();

        // Update Cache
        self.summary_cache
            .push((scc.id, entry_state, unique_exits.clone()));
        unique_exits
    }

    /// Simulates execution along a specific slice (path segment).
    pub fn simulate_slice(
        &mut self,
        start_state: &AbstractState,
        slice: &Slice,
    ) -> Vec<AbstractState> {
        let start_time = Instant::now();
        let start_alias = self.time_alias;
        let start_cons = self.time_constraint;
        let start_synth = self.time_path_synth;

        let mut active_states = vec![(start_state.clone(), 0)];
        let mut final_states = Vec::new();
        let blocks = &slice.blocks;

        while let Some((state, mut i)) = active_states.pop() {
            let t_alias_1 = Instant::now();
            state.restore_to(self.graph);
            self.time_alias += t_alias_1.elapsed();

            let mut current_path = state.path.clone();
            let mut aborted = false;

            while i < blocks.len() {
                let bb_idx = blocks[i];

                // --- Nested SCC Handling ---
                if i > 0 && self.dom_to_scc.contains_key(&bb_idx) {
                    let inner_scc = self.dom_to_scc.get(&bb_idx).unwrap().clone();
                    let mut current_inner_state = AbstractState::snapshot(self.graph);
                    current_inner_state.path = current_path.clone();

                    // Recursive call for nested SCC
                    let exit_results = self.enumerate_scc(&inner_scc, current_inner_state);
                    let mut found_match = false;

                    for (target_node, target_state) in exit_results {
                        // Check if the exit matches the slice's required path
                        if let Some(offset) = blocks[i + 1..].iter().position(|&x| x == target_node)
                        {
                            let next_pos = i + 1 + offset;
                            active_states.push((target_state, next_pos));
                            found_match = true;
                        } else if target_node == slice.end_node {
                            active_states.push((target_state, blocks.len()));
                            found_match = true;
                        }
                    }

                    if !found_match {
                        aborted = true; // No valid path through SCC
                        break;
                    }

                    aborted = true; // Current linear path effectively forks here
                    break;
                }
                // ---------------------------

                let t_alias_2 = Instant::now();
                // [Strong Update] Clear constraints for reassigned variables
                if let Some(block) = self.graph.blocks.get(bb_idx) {
                    // 1. Clear assignments
                    for &local in &block.assigned_locals {
                        self.graph.constants.remove(&local);
                    }
                    // 2. Clear function call destinations
                    if let crate::analysis::core::alias_analysis::default::block::Term::Call(
                        terminator,
                    ) = &block.terminator
                    {
                        if let rustc_middle::mir::TerminatorKind::Call { destination, .. } =
                            &terminator.kind
                        {
                            let dest_local = destination.local.as_usize();
                            self.graph.constants.remove(&dest_local);
                        }
                    }
                }

                // Execute Alias Analysis for the block
                self.graph.alias_bb(bb_idx);
                let mut dummy_map = FxHashMap::default();
                let mut dummy_set = std::collections::HashSet::default();
                self.graph
                    .alias_bbcall(bb_idx, &mut dummy_map, &mut dummy_set);
                self.time_alias += t_alias_2.elapsed();

                current_path.push(bb_idx);

                // Check constraints with next block
                if i + 1 < blocks.len() {
                    let next_bb_idx = blocks[i + 1];
                    if !self.apply_branch_constraint(bb_idx, next_bb_idx) {
                        aborted = true;
                        break;
                    }
                }
                i += 1;
            }

            if aborted {
                continue;
            }

            // Final Boundary Check
            if let Some(&last_block) = blocks.last() {
                let target = if slice.is_exit {
                    slice.end_node
                } else {
                    slice.start_node
                };
                if !self.apply_branch_constraint(last_block, target) {
                    continue;
                }
            }

            let t_alias_3 = Instant::now();
            let mut final_state = AbstractState::snapshot(self.graph);
            final_state.path = current_path;
            final_state.iter_count = state.iter_count; // Preserve iteration count
            self.time_alias += t_alias_3.elapsed();
            final_states.push(final_state);
        }

        // Time accounting fix-up
        let total_elapsed = start_time.elapsed();
        let delta_alias = self.time_alias - start_alias;
        let delta_cons = self.time_constraint - start_cons;
        let delta_synth_inner = self.time_path_synth - start_synth;

        let my_synth_time = total_elapsed
            .saturating_sub(delta_alias)
            .saturating_sub(delta_cons)
            .saturating_sub(delta_synth_inner);

        self.time_path_synth += my_synth_time;
        final_states
    }

    /// Generates loop slices (paths inside SCC leading back to header).
    pub fn find_loop_slices(&self, scc: &SccMetadata) -> Vec<Slice> {
        let mut slices = Vec::new();
        let mut current_path = Vec::new();
        let mut visited = FxHashSet::default();
        let back_edge_sources: FxHashSet<usize> = scc.back_edges.iter().cloned().collect();
        let scc_nodes: FxHashSet<usize> = scc.nodes.iter().cloned().collect();

        self.dfs_slices(
            scc.dominator,
            &scc_nodes,
            &back_edge_sources,
            &FxHashSet::default(),
            &mut current_path,
            &mut visited,
            &mut slices,
            false,
        );
        slices
    }

    /// Generates exit slices (paths leading out of SCC).
    pub fn find_exit_slices(&self, scc: &SccMetadata) -> Vec<Slice> {
        let mut slices = Vec::new();
        let mut current_path = Vec::new();
        let mut visited = FxHashSet::default();
        let scc_nodes: FxHashSet<usize> = scc.nodes.iter().cloned().collect();
        let exit_targets: FxHashSet<usize> = scc.exits.iter().cloned().collect();

        self.dfs_slices(
            scc.dominator,
            &scc_nodes,
            &FxHashSet::default(),
            &exit_targets,
            &mut current_path,
            &mut visited,
            &mut slices,
            true,
        );
        slices
    }

    /// DFS helper to find path slices.
    fn dfs_slices(
        &self,
        u: usize,
        scope_nodes: &FxHashSet<usize>,
        targets: &FxHashSet<usize>,
        exit_targets: &FxHashSet<usize>,
        path: &mut Vec<usize>,
        visited: &mut FxHashSet<usize>,
        results: &mut Vec<Slice>,
        is_exit_search: bool,
    ) {
        visited.insert(u);
        path.push(u);

        if is_exit_search {
            // For exits, check edges from u -> v where v is an exit target
            if let Some(block) = self.graph.blocks.get(u) {
                for &v in &block.next {
                    if exit_targets.contains(&v) {
                        results.push(Slice {
                            start_node: path[0],
                            end_node: v,
                            blocks: path.clone(),
                            is_exit: true,
                        });
                    }
                }
            }
        } else {
            // For loops, check if u is a back-edge source
            if targets.contains(&u) {
                results.push(Slice {
                    start_node: path[0],
                    end_node: u,
                    blocks: path.clone(),
                    is_exit: false,
                });
            }
        }

        if scope_nodes.contains(&u) {
            if let Some(block) = self.graph.blocks.get(u) {
                for &v in &block.next {
                    if !visited.contains(&v) && scope_nodes.contains(&v) {
                        self.dfs_slices(
                            v,
                            scope_nodes,
                            targets,
                            exit_targets,
                            path,
                            visited,
                            results,
                            is_exit_search,
                        );
                    }
                }
            }
        }
        path.pop();
        visited.remove(&u);
    }

    /// Validates if a transition from `source_bb` to `target_bb` is feasible under current constraints.
    /// Updates constraints (Learn) or detects conflicts (Filter).
    fn apply_branch_constraint(&mut self, source_bb: usize, target_bb: usize) -> bool {
        let t_start = Instant::now();
        let block = &self.graph.blocks[source_bb];

        match &block.terminator {
            crate::analysis::core::alias_analysis::default::block::Term::Switch(terminator) => {
                if let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind {
                    let discr_local = match discr {
                        Operand::Copy(place) | Operand::Move(place) => Some(place.local.as_usize()),
                        Operand::Constant(_) => None,
                    };

                    if let Some(mut local_id) = discr_local {
                        // 1. Identify explicit target value
                        let mut explicit_val = None;
                        for (val, target) in targets.iter() {
                            if target.as_usize() == target_bb {
                                explicit_val = Some(val as usize);
                                break;
                            }
                        }

                        // 2. Handle Binary Equation Logic (e.g., if x == 5)
                        if let Some((subject_local, subject_val)) =
                            self.find_binary_eq_origin(source_bb, local_id)
                        {
                            let switch_bool_val = if let Some(v) = explicit_val {
                                v
                            } else if targets.otherwise().as_usize() == target_bb {
                                // Infer value for 'otherwise' branch (usually 0 or 1 for booleans)
                                let has_zero = targets.iter().any(|(v, _)| v == 0);
                                if has_zero { 1 } else { 0 }
                            } else {
                                self.time_constraint += t_start.elapsed();
                                return true;
                            };

                            let root_local = self.resolve_local_in_block(source_bb, subject_local);

                            if switch_bool_val == 1 {
                                // Branch implies: variable == constant
                                if let Some(&current_val) = self.graph.constants.get(&root_local) {
                                    if current_val != subject_val {
                                        // Conflict: Constraint says X != Val, but path requires X == Val
                                        self.time_constraint += t_start.elapsed();
                                        return false;
                                    }
                                } else {
                                    // Learn: X must be Val
                                    self.graph.constants.insert(root_local, subject_val);
                                }
                            } else {
                                // Branch implies: variable != constant
                                if let Some(&current_val) = self.graph.constants.get(&root_local) {
                                    if current_val == subject_val {
                                        // Conflict: Constraint says X == Val, but path requires X != Val
                                        self.time_constraint += t_start.elapsed();
                                        return false;
                                    }
                                }
                            }
                            self.time_constraint += t_start.elapsed();
                            return true;
                        }

                        // 3. Handle standard constant propagation
                        if let Some(&origin) = self.graph.discriminants.get(&local_id) {
                            local_id = origin;
                        }
                        let root_local = self.resolve_local_in_block(source_bb, local_id);

                        if let Some(current_val) = self.get_constant_value(source_bb, root_local) {
                            if let Some(switch_val) = explicit_val {
                                if current_val != switch_val {
                                    self.time_constraint += t_start.elapsed();
                                    return false;
                                }
                            } else if targets.otherwise().as_usize() == target_bb {
                                // 'Otherwise' branch implies value is NOT any of the explicit targets
                                for (val, _) in targets.iter() {
                                    if val as usize == current_val {
                                        self.time_constraint += t_start.elapsed();
                                        return false;
                                    }
                                }
                            }
                        } else {
                            if let Some(switch_val) = explicit_val {
                                self.graph.constants.insert(root_local, switch_val);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        self.time_constraint += t_start.elapsed();
        true
    }

    /// Attempts to resolve the constant value of a local variable.
    fn get_constant_value(&self, bb: usize, local: usize) -> Option<usize> {
        if let Some(&v) = self.graph.constants.get(&local) {
            return Some(v);
        }
        self.find_constant_assignment(bb, local)
    }

    /// Scans the basic block to find if a variable was assigned a constant literal.
    fn find_constant_assignment(&self, bb: usize, local_id: usize) -> Option<usize> {
        use rustc_middle::mir::{Const, Operand, Rvalue, StatementKind};
        let body = self.graph.tcx.optimized_mir(self.graph.def_id);
        let block = &body.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(bb)];
        let tcx = self.graph.tcx;
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, self.graph.def_id);

        for stmt in block.statements.iter().rev() {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.local.as_usize() == local_id {
                    if let Rvalue::Use(Operand::Constant(c)) = rvalue {
                        if let Some(bits) = c.const_.try_eval_bits(tcx, typing_env) {
                            return Some(bits as usize);
                        }
                        match c.const_ {
                            Const::Val(val, _) => {
                                if let Some(scalar) = val.try_to_scalar_int() {
                                    return Some(scalar.to_uint(scalar.size()) as usize);
                                }
                            }
                            _ => {}
                        }
                        if let Some(val) = c.const_.try_eval_target_usize(tcx, typing_env) {
                            return Some(val as usize);
                        }
                    }
                    return None;
                }
            }
        }
        None
    }

    /// Checks if a variable is the result of a binary equality check (Eq).
    /// Returns (Subject_Var_Index, Constant_Value) if found.
    fn find_binary_eq_origin(&self, bb: usize, local_id: usize) -> Option<(usize, usize)> {
        use rustc_middle::mir::{BinOp, Operand, Rvalue, StatementKind};
        let body = self.graph.tcx.optimized_mir(self.graph.def_id);
        let block = &body.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(bb)];
        let tcx = self.graph.tcx;

        for stmt in block.statements.iter().rev() {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.local.as_usize() == local_id {
                    if let Rvalue::BinaryOp(BinOp::Eq, box (op1, op2)) = rvalue {
                        let (op_place, op_const) = match (op1, op2) {
                            (Operand::Copy(p) | Operand::Move(p), Operand::Constant(c)) => (p, c),
                            (Operand::Constant(c), Operand::Copy(p) | Operand::Move(p)) => (p, c),
                            _ => return None,
                        };

                        let typing_env =
                            rustc_middle::ty::TypingEnv::post_analysis(tcx, self.graph.def_id);
                        let val = if let Some(scalar) = op_const.const_.try_to_scalar_int() {
                            Some(scalar.to_uint(scalar.size()) as usize)
                        } else if let Some(v) = op_const.const_.try_eval_bits(tcx, typing_env) {
                            Some(v as usize)
                        } else {
                            None
                        };

                        if let Some(v) = val {
                            return Some((op_place.local.as_usize(), v));
                        }
                    }
                    return None;
                }
            }
        }
        None
    }

    /// Backtracks variable copies within a block (e.g., _2 = _1) to find the original source.
    fn resolve_local_in_block(&self, bb: usize, start_local: usize) -> usize {
        use rustc_middle::mir::{Operand, Rvalue, StatementKind};
        let body = self.graph.tcx.optimized_mir(self.graph.def_id);
        let block = &body.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(bb)];

        let mut cur_local = start_local;
        for stmt in block.statements.iter().rev() {
            if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                if place.local.as_usize() == cur_local {
                    if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = rvalue {
                        cur_local = p.local.as_usize();
                    } else {
                        break;
                    }
                }
            }
        }
        cur_local
    }

    /// Checks if a new state is "fresh" (not covered by history).
    fn is_fresh(&self, new_state: &AbstractState, history: &[AbstractState]) -> bool {
        for old_state in history {
            if self.is_substate_of(new_state, old_state) {
                return false;
            }
        }
        true
    }

    /// Checks if state `a` is semantically covered by `b` (A <= B).
    fn is_substate_of(&self, a: &AbstractState, b: &AbstractState) -> bool {
        if a.constants.len() < b.constants.len() {
            return false;
        }
        // 1. Path Constraints Check
        for (var, val_b) in &b.constants {
            match a.constants.get(var) {
                Some(val_a) => {
                    if val_a != val_b {
                        return false;
                    }
                }
                None => {
                    return false;
                }
            }
        }

        // 2. Alias Sets Inclusion Check
        for set_a in &a.alias_sets {
            if set_a.len() <= 1 {
                continue;
            }
            let mut found_container = false;
            for set_b in &b.alias_sets {
                if set_a.is_subset(set_b) {
                    found_container = true;
                    break;
                }
            }
            if !found_container {
                return false;
            }
        }
        true
    }

    fn is_covered(
        &self,
        bb: usize,
        state: &AbstractState,
        results: &FxHashMap<usize, Vec<AbstractState>>,
    ) -> bool {
        if let Some(history) = results.get(&bb) {
            return !self.is_fresh(state, history);
        }
        false
    }

    fn record_state(
        &self,
        bb: usize,
        state: AbstractState,
        results: &mut FxHashMap<usize, Vec<AbstractState>>,
    ) {
        results.entry(bb).or_insert_with(Vec::new).push(state);
    }
}
