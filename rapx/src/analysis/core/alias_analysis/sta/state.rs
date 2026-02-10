use crate::analysis::core::alias_analysis::default::graph::MopGraph;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};

/// Represents the abstract state of the program at a specific program point.
///
/// This structure holds the current alias information, path constraints (constants),
/// and the execution path history used to reach this state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbstractState {
    /// A collection of alias sets. Each set contains variable indices that may alias each other.
    pub alias_sets: Vec<FxHashSet<usize>>,

    /// A map of known constant values for variables, used for path sensitivity.
    /// Key: Variable Index, Value: Constant Value.
    pub constants: FxHashMap<usize, usize>,

    /// Records the sequence of basic blocks visited to reach this state.
    /// Used for context sensitivity and debugging.
    pub path: Vec<usize>,

    /// Tracks the number of iterations/loop depth for this state.
    /// Used to prevent infinite loops during analysis (widening/termination).
    pub iter_count: usize,
}

impl AbstractState {
    /// Creates a new, empty abstract state.
    pub fn new() -> Self {
        AbstractState {
            alias_sets: Vec::new(),
            constants: FxHashMap::default(),
            path: Vec::new(),
            iter_count: 0,
        }
    }

    /// Creates a snapshot of the current state from the `MopGraph`.
    ///
    /// # Arguments
    /// * `graph` - The graph containing the current analysis data (alias sets, constants).
    ///
    /// # Note
    /// The `path` and `iter_count` are reset in the snapshot and must be managed externally
    /// if continuity is required.
    pub fn snapshot(graph: &MopGraph) -> Self {
        AbstractState {
            alias_sets: graph.alias_sets.clone(),
            constants: graph.constants.clone(),
            path: Vec::new(),
            iter_count: 0,
        }
    }

    /// Restores this abstract state back into the `MopGraph`.
    ///
    /// This overwrites the graph's current alias sets and constants with the values
    /// stored in this state, effectively resetting the analysis context to this point.
    pub fn restore_to(&self, graph: &mut MopGraph) {
        graph.alias_sets = self.alias_sets.clone();
        graph.constants = self.constants.clone();
    }
}

/// Context for holding constraints during analysis.
#[derive(Clone, Debug)]
pub struct ConstraintContext {
    pub constraints: FxHashMap<usize, usize>,
}

impl ConstraintContext {
    pub fn new() -> Self {
        ConstraintContext {
            constraints: FxHashMap::default(),
        }
    }
}
