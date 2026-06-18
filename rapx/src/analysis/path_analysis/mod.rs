pub mod default;
pub mod graph;

use crate::utils::source::get_fn_name_byid;
use rustc_hir::def_id::DefId;
use std::fmt::{self, Display};

use crate::compat::FxHashMap;
use graph::PathGraph;

/// Format a path slice with cleanup-block annotations.
///
/// Cleanup blocks (MIR unwind/drop paths) are marked with a `*` suffix.
/// Example: `[0, 1, 2*, 3]` where block 2 is a cleanup block.
pub fn format_path_annotated(path: &[usize], graph: &PathGraph<'_>) -> String {
    let blocks: Vec<String> = path
        .iter()
        .map(|&b| {
            if graph.is_cleanup_block(b) {
                format!("{}*", b)
            } else {
                b.to_string()
            }
        })
        .collect();
    format!("[{}]", blocks.join(", "))
}

/// A prefix-tree (trie) representation of whole-CFG paths.
///
/// Shares common prefixes across paths, avoiding duplication of
/// repeated block sequences that appear in many paths.
#[derive(Debug, Clone)]
pub struct PathTree {
    root: Option<PathNode>,
    len: usize,
}

#[derive(Debug, Clone)]
pub struct PathNode {
    pub block: usize,
    pub children: Vec<PathNode>,
    pub is_path_end: bool,
}

impl PathNode {
    fn from_path(path: &[usize]) -> Self {
        let mut node = PathNode {
            block: path[0],
            children: Vec::new(),
            is_path_end: path.len() == 1,
        };
        if path.len() > 1 {
            node.children.push(PathNode::from_path(&path[1..]));
        }
        node
    }
}

impl PathTree {
    pub fn new() -> Self {
        PathTree { root: None, len: 0 }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn root(&self) -> Option<&PathNode> {
        self.root.as_ref()
    }

    /// Insert a path into the tree. Returns `true` if the path was
    /// newly added (not already present as a terminal path).
    pub fn insert(&mut self, path: &[usize]) -> bool {
        if path.is_empty() {
            return false;
        }

        match &mut self.root {
            None => {
                self.root = Some(PathNode::from_path(path));
                self.len = 1;
                true
            }
            Some(root) => {
                if root.block != path[0] {
                    return false;
                }
                if Self::insert_into(root, &path[1..]) {
                    self.len += 1;
                    true
                } else {
                    false
                }
            }
        }
    }

    fn insert_into(node: &mut PathNode, suffix: &[usize]) -> bool {
        if suffix.is_empty() {
            if node.is_path_end {
                return false;
            }
            node.is_path_end = true;
            return true;
        }

        let target = suffix[0];
        for child in &mut node.children {
            if child.block == target {
                return Self::insert_into(child, &suffix[1..]);
            }
        }

        node.children.push(PathNode::from_path(suffix));
        true
    }

    /// Check whether the given path exists as a complete path in the tree.
    pub fn contains(&self, path: &[usize]) -> bool {
        let mut node = match self.root.as_ref() {
            Some(n) => n,
            None => return false,
        };
        if node.block != path[0] {
            return false;
        }
        for &block in &path[1..] {
            node = match node.children.iter().find(|c| c.block == block) {
                Some(n) => n,
                None => return false,
            };
        }
        node.is_path_end
    }

    /// Enumerate all paths as owned `Vec<usize>`.
    pub fn iter(&self) -> PathTreeIter<'_> {
        PathTreeIter {
            stack: self
                .root
                .as_ref()
                .map(|r| vec![(r, vec![r.block])])
                .unwrap_or_default(),
        }
    }

    /// Collect all paths into a flat `Vec<Vec<usize>>`.
    pub fn to_vecs(&self) -> Vec<Vec<usize>> {
        self.iter().collect()
    }

    /// Walk the tree and call `f` with each unique prefix that ends at
    /// `target_block`. The walk stops at `target_block` (does not recurse
    /// into its children), so the callback receives the path from the root
    /// up to and including `target_block`.
    ///
    /// Returns `Ok(())` if the walk completed, or `Err(())` if `f` returned
    /// `false` to request early termination.
    pub fn walk_prefixes<F>(&self, target_block: usize, f: &mut F) -> Result<(), ()>
    where
        F: FnMut(&[usize]) -> bool,
    {
        let Some(root) = self.root.as_ref() else {
            return Ok(());
        };
        let mut path = Vec::new();
        Self::walk_prefixes_impl(root, &mut path, target_block, f)
    }

    fn walk_prefixes_impl<F>(
        node: &PathNode,
        path: &mut Vec<usize>,
        target_block: usize,
        f: &mut F,
    ) -> Result<(), ()>
    where
        F: FnMut(&[usize]) -> bool,
    {
        path.push(node.block);
        if node.block == target_block {
            let cont = f(path);
            path.pop();
            return if cont { Ok(()) } else { Err(()) };
        }
        for child in &node.children {
            Self::walk_prefixes_impl(child, path, target_block, f)?;
        }
        path.pop();
        Ok(())
    }
}

impl Default for PathTree {
    fn default() -> Self {
        Self::new()
    }
}

pub struct PathTreeIter<'a> {
    stack: Vec<(&'a PathNode, Vec<usize>)>,
}

impl<'a> Iterator for PathTreeIter<'a> {
    type Item = Vec<usize>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (node, path) = self.stack.pop()?;
            for child in node.children.iter().rev() {
                let mut child_path = path.clone();
                child_path.push(child.block);
                self.stack.push((child, child_path));
            }
            if node.is_path_end {
                return Some(path);
            }
        }
    }
}

pub struct PathMapWrapper<'a, 'tcx>(
    pub FxHashMap<DefId, PathTree>,
    pub &'a FxHashMap<DefId, PathGraph<'tcx>>,
    pub bool,
);

impl Display for PathMapWrapper<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let show_all = self.2;
        writeln!(f, "=== Print path analysis results ===")?;
        for (def_id, paths) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(f, "Function: {:?}:", fn_name)?;
            let graph = self.1.get(def_id);
            for path in paths.iter() {
                if let Some(g) = graph {
                    let reachable = g.is_path_reachable(&path);
                    if !show_all && !reachable {
                        continue;
                    }
                    let annotation = if show_all {
                        format!(" | reachable: {}", reachable)
                    } else {
                        String::new()
                    };
                    writeln!(f, "  Path {}{}", format_path_annotated(&path, g), annotation)?;
                } else {
                    writeln!(f, "  Path {:?}", path)?;
                }
            }
        }
        Ok(())
    }
}
