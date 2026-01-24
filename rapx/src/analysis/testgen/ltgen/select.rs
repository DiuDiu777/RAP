use crate::analysis::testgen::context::{ApiCall, Var};
use crate::analysis::testgen::context_builder::{is_ty_move_on_call, ContextBuilder};
use crate::analysis::testgen::ltgen::LtGen;
use crate::analysis::testgen::utils;
use rand::{self, Rng};
use rustc_hir::def_id::DefId;
use rustc_middle::ty;

impl<'tcx, 'a, R: Rng> LtGen<'tcx, 'a, R> {
    pub fn get_eligable_call(
        &self,
        fn_did: DefId,
        args: ty::GenericArgsRef<'tcx>,
        builder: &mut ContextBuilder<'tcx, 'a>,
    ) -> Option<ApiCall<'tcx>> {
        let tcx = self.tcx;

        let mut api_call = ApiCall {
            fn_did,
            args: Vec::new(),
            generic_args: args,
        };

        let fn_sig =
            utils::fn_sig_with_generic_args(api_call.fn_did(), api_call.generic_args(), tcx);

        rap_trace!(
            "check eligible api: {}",
            tcx.def_path_str_with_args(api_call.fn_did, tcx.mk_args(&api_call.generic_args()))
        );

        let mut moved_vars = Vec::new();

        let mut select_provider = |providers: &[Var], is_move| -> bool {
            const MAX_FAIL_COUNT: usize = 10;

            if providers.is_empty() {
                rap_trace!("no possible providers");
                return false;
            }

            for _ in 0..MAX_FAIL_COUNT {
                rap_trace!("select provider: {providers:?}");
                let idx = self.rng.borrow_mut().random_range(0..providers.len());
                let provider = &providers[idx];

                // the provider is moved by another arg, try again
                if !provider.is_from_input() && is_move && moved_vars.contains(provider) {
                    continue;
                }

                api_call.args.push(*provider);
                if is_move {
                    moved_vars.push(*provider);
                }
                return true;
            }
            false
        };

        // choose variable for each input arg
        for input_ty in fn_sig.inputs().iter() {
            rap_trace!("input_ty = {input_ty}");
            let providers = builder.all_possible_providers(*input_ty);

            let is_move = is_ty_move_on_call(*input_ty, tcx);
            if !select_provider(&providers, is_move) {
                return None;
            }
        }

        Some(api_call)
    }
}
