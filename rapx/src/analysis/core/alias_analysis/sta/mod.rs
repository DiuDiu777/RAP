pub mod analyzer;
pub mod decomposition;
pub mod state;
pub mod topology;

// Re-export commonly used types for easier access
pub use analyzer::HierarchicalAnalyzer;
pub use state::AbstractState;
pub use topology::{SccMetadata, Slice};
