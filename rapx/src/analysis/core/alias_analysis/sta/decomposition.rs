use super::topology::SccMetadata;
use crate::analysis::core::alias_analysis::default::graph::MopGraph;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};

/// Helper struct to perform graph decomposition logic.
pub struct GraphDecomposer<'a, 'tcx> {
    graph: &'a MopGraph<'tcx>,
}

impl<'a, 'tcx> GraphDecomposer<'a, 'tcx> {
    pub fn new(graph: &'a MopGraph<'tcx>) -> Self {
        Self { graph }
    }

    /// Decomposes the graph into a hierarchical tree of SCCs.
    pub fn build_scc_hierarchy(&self) -> (Vec<SccMetadata>, FxHashMap<usize, SccMetadata>) {
        let all_nodes: Vec<usize> = (0..self.graph.blocks.len()).collect();
        let preds = self.build_predecessors();

        let scc_tree = self.decompose_subgraph(&all_nodes, &preds, &FxHashSet::default());

        // Flatten the tree for O(1) lookup
        let mut dom_to_scc = FxHashMap::default();
        let mut queue = scc_tree.clone();
        while let Some(scc) = queue.pop() {
            if !scc.sub_sccs.is_empty() {
                queue.extend(scc.sub_sccs.clone());
            }
            dom_to_scc.insert(scc.dominator, scc);
        }

        (scc_tree, dom_to_scc)
    }

    /// Recursively decomposes a subgraph into SCCs, handling nested loops.
    fn decompose_subgraph(
        &self,
        nodes: &[usize],
        preds: &FxHashMap<usize, Vec<usize>>,
        ignored_edges: &FxHashSet<(usize, usize)>,
    ) -> Vec<SccMetadata> {
        let mut result = Vec::new();
        let components = self.run_tarjan_on_subgraph(nodes, ignored_edges);

        for comp_nodes in components {
            // Handle single node non-loop cases
            if comp_nodes.len() == 1 {
                let u = comp_nodes[0];
                let has_self_loop =
                    self.graph.blocks[u].next.contains(&u) && !ignored_edges.contains(&(u, u));
                if !has_self_loop {
                    continue;
                }
            }

            let header = self.identify_header(&comp_nodes, nodes, preds, ignored_edges);

            // Identify back-edges (edges pointing to the header)
            let mut back_edges = Vec::new();
            for &u in &comp_nodes {
                if self.graph.blocks[u].next.contains(&header) {
                    if !ignored_edges.contains(&(u, header)) {
                        back_edges.push(u);
                    }
                }
            }

            // Identify exit edges (edges pointing outside the component)
            let mut exits = Vec::new();
            let comp_set: FxHashSet<usize> = comp_nodes.iter().cloned().collect();
            for &u in &comp_nodes {
                for &target in &self.graph.blocks[u].next {
                    if !comp_set.contains(&target) {
                        exits.push(target);
                    }
                }
            }

            // Recurse: Ignore current back-edges to find nested SCCs
            let mut next_level_ignored = ignored_edges.clone();
            for &source in &back_edges {
                next_level_ignored.insert((source, header));
            }

            let sub_sccs = self.decompose_subgraph(&comp_nodes, preds, &next_level_ignored);

            let scc_meta = SccMetadata {
                id: header,
                dominator: header,
                exits,
                back_edges,
                nodes: comp_nodes,
                sub_sccs,
            };
            result.push(scc_meta);
        }
        result
    }

    /// Implements Tarjan's strongly connected components algorithm.
    fn run_tarjan_on_subgraph(
        &self,
        nodes: &[usize],
        ignored_edges: &FxHashSet<(usize, usize)>,
    ) -> Vec<Vec<usize>> {
        let mut index = 0;
        let mut stack = Vec::new();
        let mut on_stack = FxHashSet::default();
        let mut indices = FxHashMap::default();
        let mut low_links = FxHashMap::default();
        let mut sccs = Vec::new();
        let node_set: FxHashSet<usize> = nodes.iter().cloned().collect();

        for &node in nodes {
            if !indices.contains_key(&node) {
                self.strongconnect(
                    node,
                    &node_set,
                    ignored_edges,
                    &mut index,
                    &mut stack,
                    &mut on_stack,
                    &mut indices,
                    &mut low_links,
                    &mut sccs,
                );
            }
        }
        sccs
    }

    fn strongconnect(
        &self,
        v: usize,
        node_set: &FxHashSet<usize>,
        ignored_edges: &FxHashSet<(usize, usize)>,
        index: &mut usize,
        stack: &mut Vec<usize>,
        on_stack: &mut FxHashSet<usize>,
        indices: &mut FxHashMap<usize, usize>,
        low_links: &mut FxHashMap<usize, usize>,
        sccs: &mut Vec<Vec<usize>>,
    ) {
        indices.insert(v, *index);
        low_links.insert(v, *index);
        *index += 1;
        stack.push(v);
        on_stack.insert(v);

        if let Some(block) = self.graph.blocks.get(v) {
            for &w in &block.next {
                if !node_set.contains(&w) || ignored_edges.contains(&(v, w)) {
                    continue;
                }
                if !indices.contains_key(&w) {
                    self.strongconnect(
                        w,
                        node_set,
                        ignored_edges,
                        index,
                        stack,
                        on_stack,
                        indices,
                        low_links,
                        sccs,
                    );
                    let low_v = low_links[&v];
                    let low_w = low_links[&w];
                    low_links.insert(v, std::cmp::min(low_v, low_w));
                } else if on_stack.contains(&w) {
                    let low_v = low_links[&v];
                    let index_w = indices[&w];
                    low_links.insert(v, std::cmp::min(low_v, index_w));
                }
            }
        }

        if low_links[&v] == indices[&v] {
            let mut component = Vec::new();
            loop {
                let w = stack.pop().unwrap();
                on_stack.remove(&w);
                component.push(w);
                if w == v {
                    break;
                }
            }
            sccs.push(component);
        }
    }

    /// Identifies the header (entry point) of an SCC.
    /// Priority: 1. Entry from outside, 2. Node 0, 3. Lowest index.
    fn identify_header(
        &self,
        comp_nodes: &[usize],
        _scope_nodes: &[usize],
        preds: &FxHashMap<usize, Vec<usize>>,
        ignored_edges: &FxHashSet<(usize, usize)>,
    ) -> usize {
        let comp_set: FxHashSet<usize> = comp_nodes.iter().cloned().collect();
        for &node in comp_nodes {
            if let Some(predecessors) = preds.get(&node) {
                for &p in predecessors {
                    if ignored_edges.contains(&(p, node)) {
                        continue;
                    }
                    if !comp_set.contains(&p) {
                        return node;
                    }
                }
            } else if node == 0 {
                return 0;
            }
        }
        *comp_nodes.iter().min().unwrap()
    }

    fn build_predecessors(&self) -> FxHashMap<usize, Vec<usize>> {
        let mut preds = FxHashMap::default();
        for block in &self.graph.blocks {
            for &target in &block.next {
                preds
                    .entry(target)
                    .or_insert_with(Vec::new)
                    .push(block.index);
            }
        }
        preds
    }
}
