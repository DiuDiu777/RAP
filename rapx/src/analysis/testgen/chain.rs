use crate::analysis::testgen::coverage::CaseMetadata;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ChainStrategy {
    DirectSink,
    OneHop,
    MultiHop,
    HazardTemporal,
}

impl ChainStrategy {
    pub fn name(self) -> &'static str {
        match self {
            Self::DirectSink => "direct_sink",
            Self::OneHop => "one_hop",
            Self::MultiHop => "multi_hop",
            Self::HazardTemporal => "hazard_temporal",
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FeedbackStats {
    pub attempts: u64,
    pub compile_success: u64,
    pub sink_reached: u64,
    pub marker_reached: u64,
    pub miri_ub: u64,
    pub eval_error: u64,
}

impl FeedbackStats {
    pub fn record_case(&mut self, metadata: &CaseMetadata) {
        self.attempts += 1;
        if metadata.compile_success {
            self.compile_success += 1;
        }
        if !metadata.sink_markers.is_empty() {
            self.sink_reached += 1;
        }
        if !metadata.executed_contracts.is_empty() {
            self.marker_reached += 1;
        }
        if metadata.miri_ub {
            self.miri_ub += 1;
        }
        if metadata.eval_error.is_some() {
            self.eval_error += 1;
        }
    }

    fn compile_success_rate(&self) -> f32 {
        ratio(self.compile_success, self.attempts)
    }

    fn marker_rate(&self) -> f32 {
        ratio(self.marker_reached, self.attempts)
    }

    fn sink_without_ub_pressure(&self) -> f32 {
        if self.sink_reached <= self.miri_ub {
            return 0.0;
        }
        ratio(self.sink_reached - self.miri_ub, self.attempts)
    }
}

#[derive(Clone, Debug)]
pub struct StrategyWeights {
    weights: BTreeMap<ChainStrategy, f32>,
}

impl Default for StrategyWeights {
    fn default() -> Self {
        Self::new([
            (ChainStrategy::DirectSink, 0.35),
            (ChainStrategy::OneHop, 0.45),
            (ChainStrategy::MultiHop, 0.20),
            (ChainStrategy::HazardTemporal, 0.30),
        ])
    }
}

impl StrategyWeights {
    pub fn new<const N: usize>(entries: [(ChainStrategy, f32); N]) -> Self {
        Self {
            weights: entries.into_iter().collect(),
        }
    }

    pub fn get(&self, strategy: ChainStrategy) -> f32 {
        self.weights.get(&strategy).copied().unwrap_or(0.0)
    }

    fn set(&mut self, strategy: ChainStrategy, value: f32) {
        self.weights.insert(strategy, value.clamp(0.05, 2.0));
    }

    pub fn iter(&self) -> impl Iterator<Item = (ChainStrategy, f32)> + '_ {
        self.weights
            .iter()
            .map(|(strategy, weight)| (*strategy, *weight))
    }
}

#[derive(Clone, Debug)]
pub struct ChainScheduler {
    base_weights: StrategyWeights,
    adjusted_weights: StrategyWeights,
    stats: FeedbackStats,
}

impl Default for ChainScheduler {
    fn default() -> Self {
        let base_weights = StrategyWeights::default();
        Self {
            adjusted_weights: base_weights.clone(),
            base_weights,
            stats: FeedbackStats::default(),
        }
    }
}

impl ChainScheduler {
    pub fn record_case(&mut self, metadata: &CaseMetadata) {
        self.stats.record_case(metadata);
        self.recompute_weights();
    }

    pub fn priority_multiplier(&self, strategy: ChainStrategy) -> f32 {
        self.adjusted_weights.get(strategy)
    }

    pub fn stats(&self) -> &FeedbackStats {
        &self.stats
    }

    pub fn summary(&self) -> String {
        let weights = self
            .adjusted_weights
            .iter()
            .map(|(strategy, weight)| format!("{}={weight:.2}", strategy.name()))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "chain: attempts={}, compile_success={}, sink_reached={}, marker_reached={}, miri_ub={}, eval_error={}, weights=[{}]\n",
            self.stats.attempts,
            self.stats.compile_success,
            self.stats.sink_reached,
            self.stats.marker_reached,
            self.stats.miri_ub,
            self.stats.eval_error,
            weights
        )
    }

    fn recompute_weights(&mut self) {
        let compile_rate = self.stats.compile_success_rate();
        let marker_rate = self.stats.marker_rate();
        let sink_pressure = self.stats.sink_without_ub_pressure();

        let direct = self.base_weights.get(ChainStrategy::DirectSink) + 0.15 * compile_rate
            - 0.10 * sink_pressure;
        let one_hop =
            self.base_weights.get(ChainStrategy::OneHop) + 0.20 * compile_rate + 0.10 * marker_rate;
        let multi_hop = self.base_weights.get(ChainStrategy::MultiHop) + 0.35 * sink_pressure
            - 0.15 * (1.0 - compile_rate);
        let hazard = self.base_weights.get(ChainStrategy::HazardTemporal)
            + 0.20 * marker_rate
            + 0.20 * sink_pressure;

        self.adjusted_weights.set(ChainStrategy::DirectSink, direct);
        self.adjusted_weights.set(ChainStrategy::OneHop, one_hop);
        self.adjusted_weights
            .set(ChainStrategy::MultiHop, multi_hop);
        self.adjusted_weights
            .set(ChainStrategy::HazardTemporal, hazard);
    }
}

fn ratio(num: u64, denom: u64) -> f32 {
    if denom == 0 {
        0.0
    } else {
        num as f32 / denom as f32
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HazardTemporalPlan {
    pub contract_id: usize,
    pub source_fn: String,
    pub invalidator_fn: String,
    pub observer: HazardObserver,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HazardObserver {
    UseWitness,
}

impl HazardTemporalPlan {
    pub fn new(
        contract_id: usize,
        source_fn: impl Into<String>,
        invalidator_fn: impl Into<String>,
    ) -> Self {
        Self {
            contract_id,
            source_fn: source_fn.into(),
            invalidator_fn: invalidator_fn.into(),
            observer: HazardObserver::UseWitness,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn metadata(
        compile_success: bool,
        sink_markers: Vec<usize>,
        executed_contracts: Vec<usize>,
        miri_ub: bool,
    ) -> CaseMetadata {
        let mut metadata = CaseMetadata::empty("case", "/tmp/case");
        metadata.compile_success = compile_success;
        metadata.sink_markers = sink_markers;
        metadata.executed_contracts = executed_contracts;
        metadata.miri_ub = miri_ub;
        metadata
    }

    #[test]
    fn feedback_counts_case_outcomes() {
        let mut stats = FeedbackStats::default();
        stats.record_case(&metadata(true, vec![1], vec![1], false));
        assert_eq!(stats.attempts, 1);
        assert_eq!(stats.compile_success, 1);
        assert_eq!(stats.sink_reached, 1);
        assert_eq!(stats.marker_reached, 1);
        assert_eq!(stats.miri_ub, 0);
    }

    #[test]
    fn repeated_sink_without_ub_increases_multihop_weight() {
        let mut scheduler = ChainScheduler::default();
        let before = scheduler.priority_multiplier(ChainStrategy::MultiHop);
        scheduler.record_case(&metadata(true, vec![1], vec![], false));
        scheduler.record_case(&metadata(true, vec![1], vec![], false));
        let after = scheduler.priority_multiplier(ChainStrategy::MultiHop);
        assert!(after > before);
    }

    #[test]
    fn temporal_hazard_plan_records_three_phase_shape() {
        let plan = HazardTemporalPlan::new(7, "Cell::borrow", "Cell::write");
        assert_eq!(plan.contract_id, 7);
        assert_eq!(plan.observer, HazardObserver::UseWitness);
    }
}
