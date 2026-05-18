use crate::analysis::testgen::context::{ApiCall, InputHint};
use crate::analysis::testgen::context_builder::ContextBuilder;
use rustc_middle::ty::TyCtxt;

#[derive(Clone, Copy)]
pub struct GuidedAction<'a, 'tcx> {
    pub call: &'a ApiCall<'tcx>,
}

/// Pluggable fuzzing guidance. Analyses can stay independent and only expose
/// action scores plus optional concrete input hints to the generator.
pub trait FuzzGuide<'tcx> {
    fn name(&self) -> &'static str;

    fn score_action(
        &self,
        action: GuidedAction<'_, 'tcx>,
        builder: &ContextBuilder<'tcx, '_>,
    ) -> f32;

    fn input_hints_for_call(
        &self,
        call: &ApiCall<'tcx>,
        builder: &ContextBuilder<'tcx, '_>,
    ) -> Vec<Option<InputHint>>;

    fn summary(&self, _tcx: TyCtxt<'tcx>) -> String {
        format!("{}: no summary", self.name())
    }
}

#[derive(Default)]
pub struct GuideSet<'tcx> {
    guides: Vec<Box<dyn FuzzGuide<'tcx> + 'tcx>>,
}

impl<'tcx> GuideSet<'tcx> {
    pub fn new() -> Self {
        Self { guides: Vec::new() }
    }

    pub fn push(&mut self, guide: Box<dyn FuzzGuide<'tcx> + 'tcx>) {
        self.guides.push(guide);
    }

    pub fn is_empty(&self) -> bool {
        self.guides.is_empty()
    }

    pub fn score_action(&self, call: &ApiCall<'tcx>, builder: &ContextBuilder<'tcx, '_>) -> f32 {
        let action = GuidedAction { call };
        self.guides
            .iter()
            .map(|guide| guide.score_action(action, builder))
            .sum()
    }

    pub fn input_hints_for_call(
        &self,
        call: &ApiCall<'tcx>,
        builder: &ContextBuilder<'tcx, '_>,
    ) -> Vec<Option<InputHint>> {
        let mut hints = Vec::new();
        for guide in &self.guides {
            let guide_hints = guide.input_hints_for_call(call, builder);
            if guide_hints.len() > hints.len() {
                hints.resize(guide_hints.len(), None);
            }
            for (idx, hint) in guide_hints.into_iter().enumerate() {
                if hints[idx].is_none() {
                    hints[idx] = hint;
                }
            }
        }
        hints
    }

    pub fn summary(&self, tcx: TyCtxt<'tcx>) -> String {
        self.guides
            .iter()
            .map(|guide| guide.summary(tcx))
            .collect::<Vec<_>>()
            .join("\n")
    }
}
