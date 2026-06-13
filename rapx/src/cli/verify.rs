use clap::Args;

/// Arguments for the `verify` command.
#[derive(Debug, Clone, Args)]
pub struct VerifyArgs {
    /// Identify all functions annotated with #[rapx::verify] and print each target, its unsafe callees, and their safety contracts.
    #[arg(long)]
    pub prepare_targets: bool,
    /// Number of extra SCC postfix repetitions allowed during path enumeration.
    /// Default is 0 (postfix segments appear once each). Set to 1 to allow one extra repetition (two total occurrences), etc.
    #[arg(long, default_value_t = 0)]
    pub allow_pathseg_repeat: usize,
}
