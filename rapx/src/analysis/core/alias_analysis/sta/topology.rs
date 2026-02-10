/// Represents a path slice through the Control Flow Graph (CFG).
///
/// A slice can either be a loop back-edge path (within an SCC) or an exit path
/// leading out of an SCC.
#[derive(Clone, Debug)]
pub struct Slice {
    /// The starting node index of the slice.
    pub start_node: usize,
    /// The ending node index of the slice.
    pub end_node: usize,
    /// The sequence of basic blocks comprising this slice.
    pub blocks: Vec<usize>,
    /// Indicates whether this slice leads to an exit from the current SCC.
    pub is_exit: bool,
}

/// Metadata describing a Strongly Connected Component (SCC) in the CFG.
///
/// This structure supports hierarchical decomposition, allowing SCCs to contain
/// nested sub-SCCs.
#[derive(Debug, Clone)]
pub struct SccMetadata {
    /// The unique identifier for this SCC (usually the header node index).
    pub id: usize,
    /// The dominator/header node of the SCC.
    pub dominator: usize,
    /// List of target nodes that edges leaving this SCC point to.
    pub exits: Vec<usize>,
    /// List of nodes within the SCC that have back-edges to the dominator.
    pub back_edges: Vec<usize>,
    /// All nodes contained within this SCC.
    pub nodes: Vec<usize>,
    /// Nested SCCs found within this component (hierarchical structure).
    pub sub_sccs: Vec<SccMetadata>,
}
