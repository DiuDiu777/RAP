//! Alias hazard checks for unsafe view-producing APIs.
//!
//! `Alias` is more stateful than numeric SPs such as `Align`: calls like
//! `from_raw_parts_mut` create a view whose lifetime constrains later uses of
//! the original raw pointer.  This module handles the first, deliberately small
//! slice-view model:
//!
//! - a local view only checks later uses in the same function;
//! - an escaped view from `self.field` checks whether the same struct still
//!   exposes or writes through that raw field via safe methods or public fields.

use std::collections::{HashMap, HashSet};

use rustc_hir::{Safety, def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{
        BasicBlock, Local, LocalDecls, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{self, AssocKind, Ty, TyCtxt, TyKind},
};

use crate::{
    helpers::mir_scan::check_safety,
    verify::{
        def_use::{PlaceBaseKey, PlaceKey},
        call_summary::fn_simulator,
        verifier::{AbstractValue, ForwardVisitResult},
    },
};
use crate::helpers::mir_scan::{Checkpoint, CheckpointKind};
use crate::analysis::alias::{
    collect_local_origins, resolve_place, resolve_self_field_origin, LocalOriginMap,
};

use super::common::{
    SmtCheckResult, SmtChecker, call_destination, failed_smt, operand_mir_place, operand_place,
    rvalue_source_place,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HazardKind {
    SharedView,
    UniqueView,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AliasProducer {
    View(HazardKind),
    OwnershipTransfer,
    ReadMemory,
}

#[derive(Clone, Debug)]
pub(super) struct SelfFieldOrigin {
    pub(super) struct_def_id: DefId,
    pub(super) field_index: usize,
    pub(super) field_name: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RawAccessKind {
    Read,
    Write,
}

/// Determines whether a `Local(1)` origin is trivially alias-safe based on
/// the parameter type and the produced view kind. Returns `None` when the
/// origin type requires further checking (e.g., raw pointers).
fn alias_proved_for_param_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    local_index: usize,
    kind: HazardKind,
) -> Option<SmtCheckResult> {
    let body = tcx.optimized_mir(caller);
    let ty = body.local_decls[Local::from_usize(local_index)].ty;
    match ty.kind() {
        ty::Ref(_, _, ty::Mutability::Mut) => Some(SmtCheckResult::proved(
            "returned view reinterprets a &mut param; no hidden raw-pointer conflict",
        )),
        ty::Ref(_, _, ty::Mutability::Not) => {
            if kind == HazardKind::UniqueView {
                Some(failed_smt(
                    "shared reference origin cannot safely produce a unique mut view",
                ))
            } else {
                Some(SmtCheckResult::proved(
                    "returned shared view tied to shared reference; no shared alias conflict",
                ))
            }
        }
        // Owned parameter (e.g. Vec, Box): this function owns the memory;
        // the caller cannot alias it.  If local_hazard_violation found
        // nothing, there is no further alias risk.
        _ if !matches!(ty.kind(), ty::RawPtr(..)) && local_index <= body.arg_count => {
            Some(SmtCheckResult::proved(
                "returned view derives from an owned parameter; no external alias risk",
            ))
        }
        _ => None,
    }
}

/// Recursively resolve a local through the origin map until reaching a
/// terminal place (local 1 with fields, or a local without a mapping).
fn deep_resolve_place(
    mut local: usize,
    origins: &LocalOriginMap,
) -> (usize, Vec<usize>) {
    let mut seen = std::collections::HashSet::new();
    let mut all_fields: Vec<usize> = Vec::new();
    loop {
        if !seen.insert(local) {
            return (local, all_fields);
        }
        match origins.get(&local) {
            Some((l, fields)) => {
                let mut combined = fields.clone();
                combined.extend(all_fields.iter());
                all_fields = combined;
                if *l == 1 {
                    return (1, all_fields);
                }
                local = *l;
            }
            None => {
                return (local, all_fields);
            }
        }
    }
}

/// Check the path-sensitive / escaped hazard part of `Alias`.
pub fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    _forward_property: &crate::verify::contract::Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    if checkpoint.kind == CheckpointKind::RawPtrDeref && checkpoint.is_ref {
        return check_raw_ptr_deref_alias(checker, checkpoint, forward);
    }

    let Some(callee) = checkpoint.callee else {
        return SmtCheckResult::unknown("Alias target callee could not be resolved");
    };
    let callee_name = checker.tcx.def_path_str(callee);

    if callee_name.contains("::NonNull::<")
        && (callee_name.ends_with("::as_ref") || callee_name.ends_with("::as_mut"))
    {
        return check_nonnull_as_ref_alias(checker, checkpoint, forward, callee_name);
    }

    let Some(producer) = alias_producer(callee_name.as_str()) else {
        return SmtCheckResult::unknown(
            "Alias lowering currently supports view producers and ownership-transfer APIs",
        );
    };

    let Some(origin_arg) = checkpoint.args.first() else {
        return SmtCheckResult::unknown("Alias producer has no pointer argument");
    };
    let Some(origin_place) = operand_place(origin_arg) else {
        return SmtCheckResult::unknown("Alias pointer argument is not a MIR place");
    };
    let origin = resolve_forward_place(origin_place.clone(), forward);
    let mut local_origins = vec![origin_place.clone()];
    if !local_origins.contains(&origin) {
        local_origins.push(origin.clone());
    }
    let destination = call_destination(checker.tcx, checkpoint);

    if producer == AliasProducer::ReadMemory {
        if let Some(origin_arg) = checkpoint.args.first() {
            if let Some(mir_place) = operand_mir_place(origin_arg) {
                let body = checker.tcx.optimized_mir(checkpoint.caller);
                let ptr_ty = body.local_decls[mir_place.local].ty;
                if let rustc_middle::ty::TyKind::RawPtr(pointee, _) = ptr_ty.kind() {
                    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(
                        checker.tcx,
                        checkpoint.caller,
                    );
                    if checker.tcx.type_is_copy_modulo_regions(typing_env, *pointee) {
                        return SmtCheckResult::proved(
                            "read API pointee type is Copy — structural copy is safe",
                        );
                    }
                    // Non-Copy read: check if returned value escapes while source persists.
                    if let Some(dest) = destination {
                        if !destination_flows_to_return(checker.tcx, checkpoint.caller, Some(dest)) {
                            return SmtCheckResult::proved(
                                "read API value does not escape to return — no structural alias hazard",
                            );
                        }
                    }
                    let origins = collect_local_origins(checker.tcx, checkpoint.caller);
                    let (origin_local, origin_fields) =
                        deep_resolve_place(mir_place.local.as_usize(), &origins);
                    if origin_local == 1 && !origin_fields.is_empty() {
                        let mut has_from_raw = false;
                        for (_bb, data) in body.basic_blocks.iter_enumerated() {
                            if let rustc_middle::mir::TerminatorKind::Call { func, .. } = &data.terminator().kind {
                                if let rustc_middle::mir::Operand::Constant(c) = func {
                                    if let rustc_middle::ty::FnDef(def_id, _) = c.const_.ty().kind() {
                                        let name = checker.tcx.def_path_str(*def_id);
                                        if is_ownership_transfer_api(&name) {
                                            has_from_raw = true;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        if has_from_raw {
                            return failed_smt(
                                "read API value escapes, and a subsequent from_raw may double-drop the original value in the freed allocation",
                            );
                        }
                        return failed_smt(format!(
                            "returned value from read API escapes while the source pointer persists — structural alias hazard"
                        ));
                    }
                }
            }
        }
        return SmtCheckResult::proved(
            "read API creates structural aliasing between source and return value — hazard acknowledged",
        );
    }

    let AliasProducer::View(kind) = producer else {
        if let Some(reason) = ownership_transfer_violation(
            checker.tcx,
            checkpoint.caller,
            checkpoint.block,
            destination,
            &origin_place,
        ) {
            return failed_smt(reason);
        }
        return SmtCheckResult::proved(
            "ownership-transfer API consumes the raw pointer and no later raw reuse was found",
        );
    };
    // Extract the view's length argument for non-overlap reasoning
    // (from_raw_parts_mut(ptr, len) → args[1] is len).
    let view_len_place = checkpoint.args.get(1).and_then(|a| operand_place(a));

    if let Some(reason) = local_hazard_violation(
        checker.tcx,
        checkpoint.caller,
        checkpoint.block,
        destination,
        &local_origins,
        kind,
        Some(forward),
        view_len_place,
    ) {
        return failed_smt(reason);
    }

    let dest_flows = destination_flows_to_return(checker.tcx, checkpoint.caller, destination);
    if !dest_flows {
        return SmtCheckResult::proved(
            "Alias hazard is local and no conflicting raw access was found after the view producer",
        );
    }
    if let Some(sfo) = self_field_origin(checker.tcx, checkpoint.caller, &origin) {
        if let Some(reason) =
            escaped_self_field_violation(checker.tcx, checkpoint.caller, &sfo)
        {
            return failed_smt(reason);
        }
        return SmtCheckResult::proved(format!(
            "returned view is backed by private field `{}` and no safe raw-field breaker was found",
            sfo.field_name
        ));
    }

    // For struct-field origins where the field's local is not _1
    // (e.g. call-site verification), try to resolve directly.
    if let Some(sfo) = any_struct_field_origin(checker.tcx, checkpoint.caller, &origin) {
        if let Some(reason) =
            escaped_self_field_violation(checker.tcx, checkpoint.caller, &sfo)
        {
            return failed_smt(reason);
        }
        return SmtCheckResult::proved(format!(
            "returned view is backed by private field `{}` (non-_1 origin)",
            sfo.field_name
        ));
    }

    // A shared view that escapes is sound when the origin traces to a
    // reference parameter (even through struct fields) — shared refs
    // can coexist.  local_hazard_violation already confirmed no writes.
    if kind == HazardKind::SharedView {
        let param_origin = resolve_param_origin(checker.tcx, checkpoint.caller, &origin);
        if let Some(local) = param_origin {
            let check_place = PlaceKey { base: PlaceBaseKey::Local(local), fields: vec![] };
            if is_origin_a_reference(checker.tcx, checkpoint.caller, &check_place) {
                return SmtCheckResult::proved(
                    "escaped shared view from reference parameter: no conflicting writes",
                );
            }
        }
    }

    if origin.base == PlaceBaseKey::Local(1) && origin.fields.is_empty() {
        if let PlaceBaseKey::Local(local_index) = origin.base {
            if let Some(result) =
                alias_proved_for_param_local(checker.tcx, checkpoint.caller, local_index, kind)
            {
                return result;
            }
        }
    }

    // Also try tracing through reborrows (e.g. origin in a struct field
    // that ultimately comes from a reference parameter).
    let param_origin = resolve_param_origin(checker.tcx, checkpoint.caller, &origin);
    if let Some(local_index) = param_origin {
        if let Some(result) =
            alias_proved_for_param_local(checker.tcx, checkpoint.caller, local_index, kind)
        {
            return result;
        }
    }

    if let Some(result) =
        private_fn_callsite_delegation(checker.tcx, checkpoint.caller, &origin, kind)
    {
        return result;
    }

    let err_msg = format!(
        "returned view escapes while the original pointer is not owned by a private self field [origin={:?}]",
        origin
    );
    failed_smt(err_msg)
}

/// Like `self_field_origin`, but doesn't require `local == 1`.
/// Handles struct-field origins from call-site verifications.
fn any_struct_field_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    place: &PlaceKey,
) -> Option<SelfFieldOrigin> {
    let PlaceBaseKey::Local(local) = place.base else { return None; };
    if place.fields.is_empty() { return None; }
    let resolved = crate::analysis::alias::resolve_any_field_origin(
        tcx, caller, local, &place.fields,
    )?;
    Some(SelfFieldOrigin {
        struct_def_id: resolved.struct_def_id,
        field_index: resolved.field_index,
        field_name: resolved.field_name,
    })
}

/// True when the origin local's type is a reference (`&T` or `&mut T`),
/// or traces through the local origin map to a reference-typed parameter.
fn is_origin_a_reference(tcx: TyCtxt<'_>, caller: DefId, origin: &PlaceKey) -> bool {
    let body = tcx.optimized_mir(caller);
    let PlaceBaseKey::Local(mut local) = origin.base else { return false; };
    // Directly check the origin local's type.
    if let ty::Ref(..) = body.local_decls[Local::from_usize(local)].ty.kind() {
        return true;
    }
    // Trace through the local origin map — the raw pointer may have been
    // copied through intermediate locals.
    let origins = collect_local_origins(tcx, caller);
    let (resolved, _) = deep_resolve_place(local, &origins);
    if resolved >= 1 && resolved <= body.arg_count {
        local = resolved;
    }
    matches!(body.local_decls[Local::from_usize(local)].ty.kind(), ty::Ref(..))
}

/// Like `alias_proved_for_param_local`, but checks the origin local's type
/// directly (useful when the origin is a reborrowed local, not necessarily
/// `_1`).
fn alias_proved_for_param_local_from_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origin: &PlaceKey,
    kind: HazardKind,
) -> Option<SmtCheckResult> {
    let body = tcx.optimized_mir(caller);
    let local = match origin.base {
        PlaceBaseKey::Local(l) => l,
        _ => return None,
    };
    if !origin.fields.is_empty() {
        return None;
    }
    let ty = body.local_decls[Local::from_usize(local)].ty;
    match ty.kind() {
        ty::Ref(_, _, ty::Mutability::Mut) if kind == HazardKind::SharedView => {
            Some(SmtCheckResult::proved(
                "shared raw-ptr-deref view through &mut param — no read/write conflict with the view itself",
            ))
        }
        ty::Ref(_, _, ty::Mutability::Mut) => None, // UniqueView: might conflict, leave for further checking
        ty::Ref(_, _, ty::Mutability::Not) if kind == HazardKind::SharedView => {
            Some(SmtCheckResult::proved(
                "shared raw-ptr-deref view through shared reference; no alias conflict",
            ))
        }
        ty::Ref(_, _, ty::Mutability::Not) => {
            Some(failed_smt(
                "shared reference origin cannot safely produce a unique mut view",
            ))
        }
        _ => None,
    }
}

/// Try to trace a raw-pointer origin back through a call that returns a
/// pointer (e.g. `get_unchecked`, `get_unchecked_mut`) to the reference
/// parameter whose data the pointer targets.  Returns the type of that
/// reference parameter if found.
fn trace_raw_ptr_through_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    checkpoint_block: BasicBlock,
    raw_ptr: Local,
) -> Option<PlaceKey> {
    let body = tcx.optimized_mir(caller);

    // Walk backwards from the checkpoint block through unique predecessors
    // looking for the assignment that defined the raw pointer.
    let mut block = checkpoint_block;
    let mut visited = std::collections::HashSet::new();
    loop {
        if !visited.insert(block) {
            break;
        }
        for statement in body.basic_blocks[block].statements.iter().rev() {
            let rustc_middle::mir::StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, _rvalue) = assign.as_ref();
            if target.local != raw_ptr {
                continue;
            }
            // Found the assignment — is the rvalue a call result?
            // Walk further back to the call terminator.
            break;
        }
        // Check the terminator of the unique predecessor
        let predecessors = &body.basic_blocks.predecessors()[block];
        if predecessors.len() != 1 {
            break;
        }
        let prev = predecessors[0];
        let terminator = body.basic_blocks[prev].terminator();
        if let rustc_middle::mir::TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            if destination.local == raw_ptr {
                let callee_name = crate::helpers::mir_utils::call_name(tcx, func);
                if callee_name.contains("::get_unchecked") {
                    // `get_unchecked(self, slice)` / `get_unchecked_mut(self, slice)`
                    // The returned pointer targets `slice` (arg 1).
                    if let Some(slice) = args.get(1) {
                        return crate::verify::smt_check::common::operand_place(&slice.node);
                    }
                }
                break;
            }
        }
        block = prev;
    }

    None
}

/// Resolve an origin to a function parameter index (1-based local), if possible.
/// Uses both the local-origin map (deep_resolve_place) and a direct param check.
fn resolve_param_origin(
    tcx: TyCtxt<'_>,
    caller: DefId,
    origin: &PlaceKey,
) -> Option<usize> {
    let body = tcx.optimized_mir(caller);
    if let PlaceBaseKey::Local(local) = origin.base {
        // If the origin is directly a parameter, use it.
        if local >= 1 && local <= body.arg_count {
            return Some(local);
        }
        // Try to trace through local origins to reach _1.
        let origins = collect_local_origins(tcx, caller);
        let (resolved, _fields) = deep_resolve_place(local, &origins);
        if resolved >= 1 && resolved <= body.arg_count {
            return Some(resolved);
        }
    }
    None
}

/// Handle alias hazard for a reference created from a raw pointer dereference
/// (e.g. `&mut (*self.ptr).field` or `&(*self.ptr).field`).
fn check_raw_ptr_deref_alias<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let kind = if checkpoint.is_mut_ref {
        HazardKind::UniqueView
    } else {
        HazardKind::SharedView
    };

    let Some(origin_arg) = checkpoint.args.first() else {
        return SmtCheckResult::unknown("raw-ptr-deref alias: no pointer argument");
    };
    let Some(origin_place) = operand_place(origin_arg) else {
        return SmtCheckResult::unknown("raw-ptr-deref alias: pointer argument is not a MIR place");
    };
    let origin = resolve_forward_place(origin_place.clone(), forward);
    let mut local_origins = vec![origin_place.clone()];
    if !local_origins.contains(&origin) {
        local_origins.push(origin.clone());
    }
    let destination = call_destination(checker.tcx, checkpoint);

    if let Some(reason) = local_hazard_violation(
        checker.tcx,
        checkpoint.caller,
        checkpoint.block,
        destination,
        &local_origins,
        kind,
        Some(forward),
        None, // raw-ptr-deref: no len arg
    ) {
        return failed_smt(reason);
    }

    if !destination_flows_to_return(checker.tcx, checkpoint.caller, destination) {
        return SmtCheckResult::proved(
            "alias hazard from raw-ptr-deref reference is local and no conflicting raw access was found",
        );
    }

    if let Some(sfo) = self_field_origin(checker.tcx, checkpoint.caller, &origin) {
        if let Some(reason) =
            escaped_self_field_violation(checker.tcx, checkpoint.caller, &sfo)
        {
            return failed_smt(reason);
        }
        return SmtCheckResult::proved(format!(
            "returned reference from raw-ptr-deref is backed by private field `{}` and no safe raw-field breaker was found",
            sfo.field_name
        ));
    }

    // Check whether the origin traces to a function parameter (not just
    // `_1` — the raw pointer may have been re-borrowed into another local).
    let param_origin = resolve_param_origin(checker.tcx, checkpoint.caller, &origin);
    if let Some(local_index) = param_origin {
        if let Some(result) =
            alias_proved_for_param_local(checker.tcx, checkpoint.caller, local_index, kind)
        {
            return result;
        }
    }

    // If the origin local itself has a safe reference type (e.g. a reborrow
    // of a reference parameter), short-circuit.
    if let Some(result) = alias_proved_for_param_local_from_origin(
        checker.tcx, checkpoint.caller, &origin, kind,
    ) {
        return result;
    }

    // Try to trace the raw pointer backward through a `get_unchecked` /
    // `get_unchecked_mut` call to the slice reference parameter.
    if let Some(rpv_place) = operand_place(origin_arg) {
        if let Some(rpv_local) = rpv_place.local() {
            if let Some(slice_place) = trace_raw_ptr_through_call(
                checker.tcx,
                checkpoint.caller,
                checkpoint.block,
                rpv_local,
            ) {
                if let Some(slice_local) = slice_place.local() {
                    if let Some(result) = alias_proved_for_param_local(
                        checker.tcx, checkpoint.caller, slice_local.as_usize(), kind,
                    ) {
                        return result;
                    }
                }
            }
        }
    }

    // A shared view that escapes is sound when no writes conflict — shared
    // references can coexist.  The local_hazard_violation above already
    // confirmed that no conflicting writes exist.
    if kind == HazardKind::SharedView {
        return SmtCheckResult::proved(
            "escaped shared raw-ptr-deref view: no conflicting writes and shared refs may coexist",
        );
    }

    if let Some(result) =
        private_fn_callsite_delegation(checker.tcx, checkpoint.caller, &origin, kind)
    {
        return result;
    }

    let err_msg = format!(
        "returned reference from raw-ptr-deref escapes while the original pointer is not owned by a private self field [origin={:?}]",
        origin
    );
    failed_smt(err_msg)
}

/// Handle alias hazard for NonNull::as_mut / NonNull::as_ref creating a reference
/// from a NonNull pointer stored in a self field.
fn check_nonnull_as_ref_alias<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    callee_name: String,
) -> SmtCheckResult {
    let kind = if callee_name.ends_with("::as_mut") {
        HazardKind::UniqueView
    } else {
        HazardKind::SharedView
    };

    let Some(origin_arg) = checkpoint.args.first() else {
        return SmtCheckResult::unknown("NonNull::as_ref/as_mut alias: no pointer argument");
    };
    let Some(origin_place) = operand_mir_place(origin_arg) else {
        return SmtCheckResult::unknown("NonNull::as_ref/as_mut alias: pointer argument is not a MIR place");
    };

    let origins = collect_local_origins(checker.tcx, checkpoint.caller);
    let (origin_local, origin_fields) = resolve_place(origin_place, &origins);

    if origin_local != 1 || origin_fields.is_empty() {
        return SmtCheckResult::proved(
            "NonNull::as_ref/as_mut origin is not a self field — no escape hazard",
        );
    }

    let origin = PlaceKey {
        base: PlaceBaseKey::Local(origin_local),
        fields: origin_fields.clone(),
    };

    let destination = call_destination(checker.tcx, checkpoint);

    let mut local_origins = vec![PlaceKey::from_mir_place(origin_place)];
    if !local_origins.contains(&origin) {
        local_origins.push(origin.clone());
    }
    if let Some(reason) = local_hazard_violation(
        checker.tcx,
        checkpoint.caller,
        checkpoint.block,
        destination,
        &local_origins,
        kind,
        Some(forward),
        None, // NonNull::as_ref/as_mut: no len arg
    ) {
        return failed_smt(reason);
    }

    if !destination_flows_to_return(checker.tcx, checkpoint.caller, destination) {
        return SmtCheckResult::proved(
            "NonNull::as_ref/as_mut reference is local and no conflicting raw access was found",
        );
    }

    if let Some(origin) = self_field_origin(checker.tcx, checkpoint.caller, &origin) {
        if let Some(reason) =
            escaped_self_field_violation(checker.tcx, checkpoint.caller, &origin)
        {
            return failed_smt(reason);
        }
        if kind == HazardKind::UniqueView {
            if let Some(reason) =
                escaped_nonnull_as_mut_violation(checker.tcx, checkpoint.caller, &origin)
            {
                return failed_smt(reason);
            }
        }
        return SmtCheckResult::proved(format!(
            "returned reference from NonNull::as_ref/as_mut is backed by private field `{}` and no safe raw-field breaker was found",
            origin.field_name
        ));
    }

    SmtCheckResult::proved(
        "NonNull::as_ref/as_mut origin is not a self field — no escape hazard",
    )
}

/// When the view producer lives in a crate-private helper whose pointer origin
/// is a parameter, the alias obligation is discharged at each in-crate call
/// site instead: the helper itself has no local conflicting access, so the
/// hazard (if any) must appear in the caller that owns both the pointer and
/// the returned view.
fn private_fn_callsite_delegation<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origin: &PlaceKey,
    kind: HazardKind,
) -> Option<SmtCheckResult> {
    let param_index = param_index_of_origin(tcx, caller, origin)?;
    if is_externally_reachable(tcx, caller) {
        return None;
    }

    for site in local_callsites(tcx, caller) {
        let mut origins = callsite_arg_origins(tcx, site.caller, &site.args, param_index);
        if origins.is_empty() {
            continue;
        }
        let extra = as_ptr_provenance_origins(tcx, site.caller, &origins);
        for place in extra {
            if !origins.contains(&place) {
                origins.push(place);
            }
        }
        if let Some(reason) = local_hazard_violation_with(
            tcx,
            site.caller,
            site.block,
            site.destination,
            &origins,
            kind,
            true,
            None,
            None, // view_len_place: not available for cross-crate calls
        ) {
            return Some(failed_smt(format!(
                "call site `{}` conflicts with the returned view: {reason}",
                tcx.def_path_str(site.caller)
            )));
        }
    }

    Some(SmtCheckResult::proved(
        "crate-private helper: every in-crate call site keeps the original pointer unused while the view is live",
    ))
}

/// Returns the parameter index (0-based) when the resolved origin is a raw
/// pointer parameter of `caller`.
pub(super) fn param_index_of_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origin: &PlaceKey,
) -> Option<usize> {
    let PlaceBaseKey::Local(local) = origin.base else {
        return None;
    };
    if !origin.fields.is_empty() {
        return None;
    }
    let body = tcx.optimized_mir(caller);
    if local == 0 || local > body.arg_count {
        return None;
    }
    let ty = body.local_decls[Local::from_usize(local)].ty;
    matches!(ty.kind(), TyKind::RawPtr(..)).then_some(local - 1)
}

/// Returns true when the function may be called from outside this crate.
pub(super) fn is_externally_reachable<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let Some(local) = def_id.as_local() else {
        return true;
    };
    tcx.effective_visibilities(()).is_reachable(local)
}

pub(super) struct LocalCallsite<'tcx> {
    pub(super) caller: DefId,
    pub(super) block: BasicBlock,
    pub(super) args: Vec<Operand<'tcx>>,
    pub(super) destination: Option<Local>,
}

/// Finds all MIR call sites of `callee` inside the current crate.
pub(super) fn local_callsites<'tcx>(tcx: TyCtxt<'tcx>, callee: DefId) -> Vec<LocalCallsite<'tcx>> {
    let mut sites = Vec::new();
    for def_id in tcx.mir_keys(()) {
        let def_id = def_id.to_def_id();
        if def_id == callee {
            continue;
        }
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        if !tcx.is_mir_available(def_id) {
            continue;
        }
        let body = tcx.optimized_mir(def_id);
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let Some(terminator) = &data.terminator else {
                continue;
            };
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            else {
                continue;
            };
            let Some(target) = call_target_def_id(func) else {
                continue;
            };
            if target != callee {
                continue;
            }
            sites.push(LocalCallsite {
                caller: def_id,
                block,
                args: args.iter().map(|arg| arg.node.clone()).collect(),
                destination: Some(destination.local),
            });
        }
    }
    sites
}

fn call_target_def_id<'tcx>(func: &Operand<'tcx>) -> Option<DefId> {
    let Operand::Constant(constant) = func else {
        return None;
    };
    match constant.const_.ty().kind() {
        TyKind::FnDef(def_id, _) => Some(*def_id),
        _ => None,
    }
}

/// Resolves the actual argument passed for `param_index` at a call site.
pub(super) fn callsite_arg_origins<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    args: &[Operand<'tcx>],
    param_index: usize,
) -> Vec<PlaceKey> {
    let Some(arg) = args.get(param_index) else {
        return Vec::new();
    };
    let Some(place) = (match arg {
        Operand::Copy(place) | Operand::Move(place) => Some(PlaceKey::from_mir_place(place)),
        Operand::Constant(_) => None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => None,
    }) else {
        return Vec::new();
    };
    let aliases = collect_place_aliases(tcx, caller);
    let mut origins = vec![place.clone()];
    if let Some(local) = place.local() {
        if let Some(alias) = aliases.get(&local) {
            if !origins.contains(alias) {
                origins.push(alias.clone());
            }
        }
    }
    origins
}

/// Scan all blocks for `as_ptr`/`as_mut_ptr` calls whose destination overlaps
/// any of `origins`. Returns the resolved receiver places.
fn find_as_ptr_receivers<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
    check_alias_dest: bool,
) -> Vec<PlaceKey> {
    let body = tcx.optimized_mir(caller);
    let mut result = Vec::new();
    for block in body.basic_blocks.iter() {
        let Some(terminator) = &block.terminator else { continue };
        let TerminatorKind::Call { func, args, destination, .. } = &terminator.kind else {
            continue;
        };
        let name = crate::helpers::mir_utils::call_name(tcx, func);
        if !fn_simulator::is_as_ptr(&name) {
            continue;
        }
        let destination_key = PlaceKey {
            base: PlaceBaseKey::Local(destination.local.as_usize()),
            fields: Vec::new(),
        };
        let dest_overlaps = || {
            origins.iter().any(|origin| destination_key.overlaps(origin))
                || (check_alias_dest
                    && aliases
                        .get(&destination.local)
                        .is_some_and(|alias| origins.iter().any(|o| alias.overlaps(o))))
        };
        if !dest_overlaps() {
            continue;
        }
        let Some(receiver) = args.first() else { continue };
        let Some(place) = operand_mir_place(&receiver.node) else { continue };
        let resolved = resolve_mir_place(place, aliases);
        if !result.contains(&resolved) {
            result.push(resolved);
        }
    }
    result
}

/// Adds the receiver of `as_ptr`/`as_mut_ptr` calls that produced any of the
/// current origin locals, so writes through the original owner are also seen.
pub(super) fn as_ptr_provenance_origins<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origins: &[PlaceKey],
) -> Vec<PlaceKey> {
    let aliases = collect_place_aliases(tcx, caller);
    find_as_ptr_receivers(tcx, caller, origins, &aliases, false)
}

fn alias_producer(name: &str) -> Option<AliasProducer> {
    if name.contains("from_raw_parts_mut") {
        return Some(AliasProducer::View(HazardKind::UniqueView));
    }
    if name.contains("from_raw_parts") || name.contains("from_parts") || name.contains("from_ptr") {
        if is_vec_ownership_transfer_api(name) {
            return Some(AliasProducer::OwnershipTransfer);
        }
        return Some(AliasProducer::View(HazardKind::SharedView));
    }
    if is_ownership_transfer_api(name) {
        return Some(AliasProducer::OwnershipTransfer);
    }
    if is_read_api(name) {
        return Some(AliasProducer::ReadMemory);
    }
    None
}

fn is_read_api(name: &str) -> bool {
    if name.contains("::ptr::") {
        if name.ends_with("::read")
            || name.ends_with("::read_unaligned")
            || name.ends_with("::read_volatile")
            || name.ends_with("::copy_to")
            || name.ends_with("::copy_to_nonoverlapping")
            || name.ends_with("::copy_from")
            || name.ends_with("::copy_from_nonoverlapping")
        {
            return true;
        }
    }
    if name.ends_with("::assume_init_read") {
        return true;
    }
    if name.contains("::intrinsics::")
        && (name.ends_with("::copy") || name.ends_with("::copy_nonoverlapping"))
    {
        return true;
    }
    false
}

fn is_ownership_transfer_api(name: &str) -> bool {
    if is_vec_ownership_transfer_api(name) {
        return true;
    }
    let is_from_raw = name.contains("from_raw");
    is_from_raw
        && (name.contains("boxed")
            || name.contains("Box")
            || name.contains("ffi::c_str")
            || name.contains("CString")
            || is_vec_ownership_transfer_api(name))
}

fn is_vec_ownership_transfer_api(name: &str) -> bool {
    (name.contains("from_raw_parts") || name.contains("from_parts"))
        && (name.contains("Vec") || name.contains("vec::"))
}

pub(super) fn resolve_forward_place<'tcx>(
    mut place: PlaceKey,
    forward: &ForwardVisitResult<'tcx>,
) -> PlaceKey {
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(place.clone()) {
            return place;
        }
        let Some(local) = place.local() else {
            return place;
        };
        let Some(value) = forward.values.get(&local) else {
            return place;
        };
        match value {
            AbstractValue::Place(next) | AbstractValue::Ref(next) | AbstractValue::RawPtr(next) => {
                place = next.clone();
            }
            AbstractValue::Cast(inner, _) => match inner.as_ref() {
                AbstractValue::Place(next)
                | AbstractValue::Ref(next)
                | AbstractValue::RawPtr(next) => place = next.clone(),
                _ => return place,
            },
            AbstractValue::CallResult(call)
                if fn_simulator::is_as_ptr(&call.func) =>
            {
                let Some(source) = forward.points_to_graph.get_source(&place) else {
                    return place;
                };
                place = resolve_forward_place(source.clone(), forward);
            }
            AbstractValue::CallResult(call)
                if fn_simulator::is_pointer_arithmetic(&call.func) =>
            {
                let Some(source) = forward.points_to_graph.get_source(&place) else {
                    return place;
                };
                place = resolve_forward_place(source.clone(), forward);
            }
            _ => return place,
        }
    }
}

fn destination_flows_to_return<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    destination: Option<Local>,
) -> bool {
    let Some(destination) = destination else {
        return false;
    };
    if destination.as_usize() == 0 {
        return true;
    }

    let body = tcx.optimized_mir(caller);
    if body.local_decls[Local::from_usize(0)].ty == body.local_decls[destination].ty {
        return true;
    }

    let mut aliases: HashMap<Local, PlaceKey> = HashMap::new();
    aliases.insert(
        destination,
        PlaceKey {
            base: PlaceBaseKey::Local(destination.as_usize()),
            fields: Vec::new(),
        },
    );

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local.as_usize() == 0 {
                if rvalue_mentions_local(rvalue, destination, &aliases) {
                    return true;
                }
            }
            if rvalue_mentions_local(rvalue, destination, &aliases) {
                aliases.insert(target.local, aliases[&destination].clone());
            }
        }
    }
    false
}

fn rvalue_any_place_matching<'tcx>(
    rvalue: &Rvalue<'tcx>,
    pred: &mut impl FnMut(&Place<'tcx>) -> bool,
) -> bool {
    match rvalue {
        Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => pred(place),
            Operand::Constant(_) => false,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => false,
        }),
        _ => rvalue_source_place(rvalue).map_or(false, |place| pred(place)),
    }
}

fn rvalue_mentions_local<'tcx>(
    rvalue: &Rvalue<'tcx>,
    local: Local,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| {
        place.local == local || aliases.contains_key(&place.local)
    })
}

fn local_hazard_violation<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origins: &[PlaceKey],
    kind: HazardKind,
    forward: Option<&ForwardVisitResult<'tcx>>,
    view_len_place: Option<PlaceKey>,
) -> Option<String> {
    local_hazard_violation_with(tcx, caller, call_block, destination, origins, kind, false, forward, view_len_place)
}

fn local_hazard_violation_with<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origins: &[PlaceKey],
    kind: HazardKind,
    strict_call_escape: bool,
    _forward: Option<&ForwardVisitResult<'tcx>>,
    view_len_place: Option<PlaceKey>,
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let mut aliases = collect_place_aliases(tcx, caller);
    let mut origins = origins.to_vec();
    expand_origin_aliases(&aliases, &mut origins);
    let mut hazard_locals: HashSet<Local> = destination.into_iter().collect();
    expand_hazard_alias_locals(tcx, caller, &mut hazard_locals);
    // Pre-populate hazard_locals with all split_at / split_at_mut results,
    // since those views are non-overlapping by definition and their
    // creation site is before the current checkpoint (so the forward scan
    // won't encounter the call terminator).
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator {
            if let TerminatorKind::Call { func, destination, .. } = &terminator.kind {
                let name = crate::helpers::mir_utils::call_name(tcx, func);
                if name.contains("::split_at") {
                    hazard_locals.insert(destination.local);
                }
            }
        }
    }
    // Remove any origin whose base local is the view itself (hazard_locals).
    // The view reading/writing its own memory is intended usage, not a
    // conflicting raw-pointer access.
    origins.retain(|origin| {
        !origin
            .local()
            .is_some_and(|l| hazard_locals.contains(&l))
    });
    let vec_owners = vec_owners_for_origins(tcx, caller, &origins, &aliases);
    let reachable = blocks_reachable_after_call(tcx, caller, call_block);

    for (block_index, block) in reverse_postorder_blocks(body) {
        if !reachable.contains(&block_index) {
            continue;
        }

        for (statement_index, statement) in block.statements.iter().enumerate() {
            match &statement.kind {
                StatementKind::StorageDead(local) => {
                    hazard_locals.remove(local);
                }
                StatementKind::Assign(assign) => {
                    let (target, rvalue) = assign.as_ref();
                    if rvalue_mentions_any_local(rvalue, &hazard_locals) {
                        let target_ty = body.local_decls[target.local].ty;
                        if matches!(target_ty.kind(), TyKind::Ref(_, _, _) | TyKind::RawPtr(_, _)) {
                            hazard_locals.insert(target.local);
                        }
                    }
                    if let Some(alias) = alias_from_rvalue(tcx, caller, rvalue, &aliases) {
                        aliases.insert(target.local, alias);
                    }
                    if !hazard_locals.is_empty()
                        && !hazard_locals.contains(&target.local)
                        && raw_access_conflicts(kind, RawAccessKind::Write)
                        && place_is_raw_access_to_any_origin(target, &origins, &aliases, &body.local_decls)
                        && hazard_used_after_statement(
                            tcx,
                            caller,
                            block_index,
                            statement_index,
                            &hazard_locals,
                        )
                    {
                        return Some(format!(
                            "raw write through original pointer after {:?} view creation",
                            kind
                        ));
                    }
                    if !hazard_locals.is_empty()
                        && !hazard_locals.contains(&target.local)
                        && raw_access_conflicts(kind, RawAccessKind::Read)
                        && !rvalue_has_hazard_local_base(rvalue, &hazard_locals)
                        && !rvalue_reads_like_view(rvalue, tcx, caller, &origins, &aliases)
                        && rvalue_reads_any_origin(rvalue, &origins, &aliases, &body.local_decls)
                        && hazard_used_after_statement(
                            tcx,
                            caller,
                            block_index,
                            statement_index,
                            &hazard_locals,
                        )
                    {
                        return Some(format!(
                            "raw read through original pointer after {:?} view creation",
                            kind
                        ));
                    }
                }
                _ => {}
            }
        }

        if !hazard_locals.is_empty() {
            let Some(terminator) = &block.terminator else {
                continue;
            };
            if origins.iter().any(|origin| {
                terminator_writes_origin(tcx, caller, &terminator.kind, origin, &aliases)
                    && !is_ownership_transfer_terminator(tcx, &terminator.kind)
            }) && hazard_used_after_block(tcx, caller, block_index, &hazard_locals)
            {
                return Some(format!(
                    "raw write call through original pointer after {:?} view creation",
                    kind
                ));
            }
            if kind == HazardKind::UniqueView
                && !vec_owners.is_empty()
                && terminator_invalidates_vec_owner(
                    tcx,
                    caller,
                    &terminator.kind,
                    &vec_owners,
                    &aliases,
                )
                && hazard_used_after_block(tcx, caller, block_index, &hazard_locals)
            {
                return Some(
                    "Vec may reallocate while a raw-derived mutable view is still live".to_string(),
                );
            }
            if strict_call_escape
                && block_index != call_block
                && !terminator_is_benign_origin_use(tcx, &terminator.kind)
                && origins.iter().any(|origin| {
                    terminator_uses_origin(tcx, caller, &terminator.kind, origin, &aliases)
                })
                && hazard_used_after_block(tcx, caller, block_index, &hazard_locals)
            {
                return Some(format!(
                    "raw pointer escapes to another call while the {:?} view is live",
                    kind
                ));
            }
            // When another from_raw_parts[_mut] call's pointer arg was
            // created by ptr::add, the views are likely non-overlapping.
            // Add its destination to hazard_locals so reads through it
            // are skipped by rvalue_has_hazard_local_base.
            if view_len_place.is_some() {
                if let TerminatorKind::Call { func, args, destination: call_dest, .. } = &terminator.kind {
                    let name = crate::helpers::mir_utils::call_name(tcx, func);
                    // from_raw_parts / from_raw_parts_mut: absorb if pointer was forwarded
                    if fn_simulator::is_from_raw_parts(&name) && args.len() >= 1 {
                        if let Some(ptr_place) = operand_place(&args[0].node) {
                            let offset_eq = is_ptr_add_offset_eq(tcx, caller, &ptr_place, view_len_place.as_ref().unwrap(), &origins);
                            let from_add = is_ptr_from_ptr_add(tcx, caller, &ptr_place);
                            if offset_eq || from_add {
                                hazard_locals.insert(call_dest.local);
                                continue;
                            }
                        }
                    }
                    // split_at / split_at_mut: both returned views are
                    // non-overlapping parts of the same allocation.
                    if name.contains("::split_at") {
                        hazard_locals.insert(call_dest.local);
                    }
                }
            }
        }
    }

    None
}

/// Check if `ptr_place` was created by `ptr::add` from any origin, and the
/// add offset argument equals `view_len`.
fn is_ptr_add_offset_eq(
    tcx: TyCtxt<'_>,
    caller: DefId,
    ptr_place: &PlaceKey,
    view_len: &PlaceKey,
    _origins: &[PlaceKey],
) -> bool {
    let body = tcx.optimized_mir(caller);
    let origins_map = collect_local_origins(tcx, caller);
    // Trace both places to their roots for structural comparison across
    // local copies produced by MIR lowering.
    let view_len_root = trace_place_root(&origins_map, view_len);
    // Walk backwards through the MIR to find where ptr_place was defined.
    // Look for a call to ptr::add whose result is ptr_place.
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        if let TerminatorKind::Call { func, args, destination, .. } = &data.terminator().kind {
            let ptr_key = PlaceKey::from_mir_place(destination);
            if ptr_key != *ptr_place {
                continue;
            }
            let name = crate::helpers::mir_utils::call_name(tcx, func);
            if fn_simulator::is_pointer_add(&name) && args.len() >= 2 {
                if let Some(offset_place) = operand_place(&args[1].node) {
                    let offset_root = trace_place_root(&origins_map, &offset_place);
                    return offset_root == view_len_root;
                }
            }
        }
    }
    false
}

/// Check if `ptr_place` was simply created by `ptr::add` — the pointer
/// was forwarded, so views from it start at a later position than views
/// from the original base pointer.
fn is_ptr_from_ptr_add(
    tcx: TyCtxt<'_>,
    caller: DefId,
    ptr_place: &PlaceKey,
) -> bool {
    let body = tcx.optimized_mir(caller);
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        if let TerminatorKind::Call { func, destination, .. } = &data.terminator().kind {
            let ptr_key = PlaceKey::from_mir_place(destination);
            if ptr_key != *ptr_place {
                continue;
            }
            let name = crate::helpers::mir_utils::call_name(tcx, func);
            return fn_simulator::is_pointer_add(&name);
        }
    }
    false
}

/// Trace a PlaceKey through the local origin map to find its root,
/// normalizing copies produced by MIR lowering.
fn trace_place_root(origins: &LocalOriginMap, place: &PlaceKey) -> Option<(usize, Vec<usize>)> {
    let Some(local) = place.local() else { return None };
    let (root_local, root_fields) = deep_resolve_place(local.as_usize(), origins);
    Some((root_local, root_fields))
}

/// Calls that read pointer metadata without granting memory access.
fn terminator_is_benign_origin_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &TerminatorKind<'tcx>,
) -> bool {
    let TerminatorKind::Call { func, .. } = terminator else {
        return true;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    fn_simulator::is_as_ptr(&name)
        || name.ends_with("::len")
        || name.ends_with("::is_empty")
        || name.ends_with("::is_null")
        || name.ends_with("::addr")
        || name.ends_with("::cast")
}

fn reverse_postorder_blocks<'a, 'tcx>(
    body: &'a rustc_middle::mir::Body<'tcx>,
) -> impl Iterator<Item = (BasicBlock, &'a rustc_middle::mir::BasicBlockData<'tcx>)> {
    rustc_middle::mir::traversal::reverse_postorder(body).map(|(block, data)| (block, data))
}

/// Walk backward from the ownership-transfer call through unique predecessors.
/// If a preceding view-producer (as_ref, as_mut) references the same origin
/// AND its destination is still alive at the transfer point, the transfer
/// conflicts with the still-live view.
fn pre_existing_view_on_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    reachable_after: &HashSet<BasicBlock>,
    origin_holders: &[PlaceKey],
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let origins = collect_local_origins(tcx, caller);

    // Collect the resolved structural origins for the holders.
    let holder_origins: Vec<(usize, Vec<usize>)> = origin_holders
        .iter()
        .flat_map(|h| {
            if let PlaceBaseKey::Local(l) = h.base {
                let resolved = resolve_place_for_key(l, &h.fields, &origins);
                if resolved.0 == 1 && !resolved.1.is_empty() {
                    Some(resolved)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    // Scan all basic blocks that are NOT reachable *after* the transfer
    // (i.e. blocks that execute before or at the transfer).
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if reachable_after.contains(&bb) || bb == call_block {
            continue;
        }

        // --- Call terminators: NonNull::as_ref / as_mut ---
        let terminator = data.terminator();
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            let callee_name = crate::helpers::mir_utils::call_name(tcx, func);
            if callee_name.contains("::NonNull::<")
                && (callee_name.ends_with("::as_ref") || callee_name.ends_with("::as_mut"))
            {
                if let Some(arg) = args.first()
                    && let Some(place) = operand_mir_place(&arg.node)
                {
                    let arg_resolved = resolve_place(place, &origins);
                    if arg_resolved.0 == 1
                        && !arg_resolved.1.is_empty()
                        && holder_origins.iter().any(|(h, hf)| {
                            *h == arg_resolved.0 && *hf == arg_resolved.1
                        })
                    {
                        return Some(format!(
                            "pre-existing view from {} aliases the ownership-transferred pointer",
                            callee_name,
                        ));
                    }
                }
            }
        }

        // --- Statements: &*raw_ptr or raw-ptr-cast that creates a view ---
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (_, rvalue) = assign.as_ref();

            // &*raw_ptr → Rvalue::Ref with Deref projection
            let src_place: Option<&Place<'tcx>> = match rvalue {
                Rvalue::Ref(_, _, place) => Some(place),
                // raw-ptr-to-reference cast: *mut T → &T via PtrToPtr
                Rvalue::Cast(kind, _, _)
                    if matches!(kind, rustc_middle::mir::CastKind::PtrToPtr) =>
                {
                    extract_cast_source_place_for_ptr_to_ptr(tcx, &statement.kind)
                }
                _ => None,
            };
            let Some(place) = src_place else { continue };

            if !place
                .projection
                .iter()
                .any(|p| matches!(p, ProjectionElem::Deref))
            {
                continue;
            }
            let resolved = resolve_place(place, &origins);
            if resolved.0 == 1
                && !resolved.1.is_empty()
                && holder_origins.iter().any(|(h, hf)| *h == resolved.0 && *hf == resolved.1)
            {
                return Some(
                    "pre-existing &*raw_ptr view aliases the ownership-transferred pointer"
                        .to_string(),
                );
            }
        }
    }
    None
}

/// When the compiler lowers `&*raw_ptr` to a `PtrToPtr` cast (`_r = raw as
/// *const ()`), the cast rvalue doesn't carry the source place.  Walk the
/// operand to recover the underlying place that was dereferenced.
fn extract_cast_source_place_for_ptr_to_ptr<'tcx>(
    _tcx: TyCtxt<'tcx>,
    kind: &'tcx rustc_middle::mir::StatementKind<'tcx>,
) -> Option<&'tcx Place<'tcx>> {
    let StatementKind::Assign(assign) = kind else {
        return None;
    };
    let (_, rvalue) = assign.as_ref();
    if let Rvalue::Cast(_, operand, _) = rvalue {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            _ => None,
        }
    } else {
        None
    }
}

/// Like `resolve_place` but for a PlaceKey (local + fields) instead of a MIR Place.
fn resolve_place_for_key(
    local: usize,
    local_fields: &[usize],
    origins: &LocalOriginMap,
) -> (usize, Vec<usize>) {
    if !local_fields.is_empty() {
        return (local, local_fields.to_vec());
    }
    origins
        .get(&local)
        .cloned()
        .unwrap_or((local, local_fields.to_vec()))
}


fn ownership_transfer_violation<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origin_place: &PlaceKey,
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let mut owner_locals: HashSet<Local> = destination.into_iter().collect();
    expand_hazard_alias_locals(tcx, caller, &mut owner_locals);
    let reachable = blocks_reachable_after_call(tcx, caller, call_block);

    // When any post-call block hands ownership back to a raw pointer via an
    // `into_raw`-style call on the owning value, later raw uses are governed
    // by that new transfer rather than this checkpoint.
    for block_index in &reachable {
        if let Some(terminator) = &body.basic_blocks[*block_index].terminator
            && terminator_returns_ownership(tcx, &terminator.kind, &owner_locals)
        {
            return None;
        }
    }

    let origins = places_holding_transferred_pointer(tcx, caller, call_block, origin_place);

    // Check for a pre-existing view (as_ref/as_mut/&*ptr) on the same origin
    // whose result is still alive when the ownership transfer occurs.
    if let Some(reason) =
        pre_existing_view_on_origin(tcx, caller, call_block, &reachable, &origins)
    {
        return Some(reason);
    }

    // Flow-sensitive forward scan from the transfer call.  Each CFG edge
    // carries the set of still-live origin places; an origin dies as soon as
    // its place is strongly redefined (a `Deref`-free assignment or call
    // destination) or its storage ends, and a copy of a live origin value
    // revives its target.  Loop back-edges therefore stop flagging reads of
    // *re-assigned* locals in later iterations as reuse of the transferred
    // pointer, while straight-line reuse is still detected.
    let start = match &body.basic_blocks[call_block].terminator().kind {
        TerminatorKind::Call {
            target: Some(target),
            ..
        } => *target,
        _ => return None,
    };

    let mut entry_states: HashMap<BasicBlock, Vec<PlaceKey>> = HashMap::new();
    let mut worklist: Vec<(BasicBlock, Vec<PlaceKey>)> = vec![(start, origins)];

    while let Some((block_index, incoming)) = worklist.pop() {
        let mut live = match entry_states.get_mut(&block_index) {
            Some(known) => {
                let mut changed = false;
                for origin in &incoming {
                    if !known.contains(origin) {
                        known.push(origin.clone());
                        changed = true;
                    }
                }
                if !changed {
                    continue;
                }
                known.clone()
            }
            None => {
                entry_states.insert(block_index, incoming.clone());
                incoming
            }
        };

        let block = &body.basic_blocks[block_index];
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(assign) => {
                    let (target, rvalue) = assign.as_ref();

                    // Writing to a place that exactly holds a transferred-origin
                    // pointer is a legitimate overwrite (e.g. `self.head = next`
                    // after `Box::from_raw(old_head)`), not a reuse violation.
                    // But we must NOT kill when the only "match" is via a
                    // Deref projection with no field access (e.g. `*raw = val`)
                    // because then the raw pointer is being dereferenced to
                    // write to the pointee, which IS a violation.
                    let target_key = PlaceKey::from_mir_place(target);
                    let is_deref_to_pointee = target_key.fields.is_empty()
                        && target
                            .projection
                            .iter()
                            .any(|p| matches!(p, ProjectionElem::Deref));
                    if !is_deref_to_pointee {
                        live.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
                    }

                    if place_is_raw_access_to_live_origin(target, &live)
                        || rvalue_reads_live_origin(rvalue, &live)
                    {
                        return Some(
                            "raw pointer reused after ownership was transferred to an owning value"
                                .to_string(),
                        );
                    }
                    let copies_origin = rvalue_copies_live_origin_value(rvalue, &live);
                    kill_strongly_updated_origins(&body.local_decls, target, &mut live);
                    if copies_origin
                        && !target
                            .projection
                            .iter()
                            .any(|projection| matches!(projection, ProjectionElem::Deref))
                    {
                        let target_key = PlaceKey::from_mir_place(target);
                        if !live.contains(&target_key) {
                            live.push(target_key);
                        }
                    }
                }
                StatementKind::StorageDead(local) => {
                    live.retain(|origin| origin.base != PlaceBaseKey::Local(local.as_usize()));
                }
                _ => {}
            }
        }

        let Some(terminator) = &block.terminator else {
            continue;
        };
        if terminator_uses_live_origin(&terminator.kind, &live) {
            return Some(
                "raw pointer passed to another call after ownership was transferred".to_string(),
            );
        }
        if let TerminatorKind::Call {
            destination: call_destination,
            ..
        } = &terminator.kind
        {
            kill_strongly_updated_origins(&body.local_decls, call_destination, &mut live);
        }
        if live.is_empty() {
            continue;
        }
        for successor in terminator.successors() {
            worklist.push((successor, live.clone()));
        }
    }

    None
}

/// Collect the places that still hold the transferred pointer *value* when
/// the ownership-transfer call executes.
///
/// Starting from the callee argument, this walks the call block (and its
/// unique-predecessor chain) backwards, following value copies while a
/// kill-set records locals that are re-assigned between a definition and the
/// call: such stale locals no longer hold the pointer at the call and must
/// not seed the reuse scan.  This keeps loop-carried locals (re-assigned each
/// iteration) out of the origin set while straight-line aliases stay in.
fn places_holding_transferred_pointer<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    origin_place: &PlaceKey,
) -> Vec<PlaceKey> {
    let body = tcx.optimized_mir(caller);
    let mut holders = vec![origin_place.clone()];
    let mut killed: HashSet<Local> = HashSet::new();
    let mut block_index = call_block;

    loop {
        let block = &body.basic_blocks[block_index];
        for statement in block.statements.iter().rev() {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target
                .projection
                .iter()
                .any(|projection| matches!(projection, ProjectionElem::Deref))
            {
                continue;
            }
            let target_key = PlaceKey::from_mir_place(target);
            let target_defines_holder =
                !killed.contains(&target.local) && holders.iter().any(|h| target_key.overlaps(h));

            let source_place = rvalue_source_place(rvalue);

            if target_defines_holder {
                // This is the latest pre-call definition of a holder: the
                // value came from the rvalue source, which therefore also
                // holds the pointer unless it was re-assigned afterwards.
                if let Some(source) = source_place
                    && !killed.contains(&source.local)
                {
                    let source_key = PlaceKey::from_mir_place(source);
                    for holder in holders.clone() {
                        if let Some(spliced) =
                            splice_holder_fields(&target_key, &holder, &source_key)
                            && !holders.contains(&spliced)
                        {
                            holders.push(spliced);
                        }
                    }
                }
            } else if let Some(source) = source_place
                && !killed.contains(&target.local)
                && !source
                    .projection
                    .iter()
                    .any(|projection| matches!(projection, ProjectionElem::Deref))
            {
                // A pre-call copy *out of* a holder: the target received the
                // pointer value earlier and has not been re-assigned since,
                // so it still holds it at the call.
                let source_key = PlaceKey::from_mir_place(source);
                if holders.iter().any(|h| source_key.overlaps(h)) && !holders.contains(&target_key)
                {
                    holders.push(target_key.clone());
                }
            }
            killed.insert(target.local);
        }

        // Step to the unique predecessor and account for its terminator.
        let predecessors = &body.basic_blocks.predecessors()[block_index];
        if predecessors.len() != 1 {
            break;
        }
        block_index = predecessors[0];
        let terminator = body.basic_blocks[block_index].terminator();
        if let TerminatorKind::Call {
            func,
            args,
            destination: call_destination,
            ..
        } = &terminator.kind
        {
            let destination_key = PlaceKey::from_mir_place(call_destination);
            if !killed.contains(&call_destination.local)
                && holders.iter().any(|h| destination_key.overlaps(h))
            {
                let name = crate::helpers::mir_utils::call_name(tcx, func);
                if fn_simulator::is_as_ptr(&name)
                    && let Some(arg) = args.first()
                    && let Operand::Copy(place) | Operand::Move(place) = &arg.node
                    && !killed.contains(&place.local)
                {
                    let key = PlaceKey::from_mir_place(place);
                    if !holders.contains(&key) {
                        holders.push(key);
                    }
                }
            }
            killed.insert(call_destination.local);
        }
    }

    holders
}

/// Rebase `holder` (a place rooted at `target`) onto `source`, keeping the
/// projection suffix that extends past the assignment target.
fn splice_holder_fields(
    target: &PlaceKey,
    holder: &PlaceKey,
    source: &PlaceKey,
) -> Option<PlaceKey> {
    if !place_key_is_prefix_of(target, holder) {
        return None;
    }
    let mut fields = source.fields.clone();
    fields.extend_from_slice(&holder.fields[target.fields.len()..]);
    Some(PlaceKey {
        base: source.base.clone(),
        fields,
    })
}

/// Remove origins invalidated by a strong update of `target`.
///
/// A `Deref`-free assignment fully redefines the assigned place, so any origin
/// it is a prefix of no longer holds the transferred pointer.  Writes through
/// pointers (`(*p).f = ...`) do not redefine the pointer-holding place itself
/// and keep every origin alive.
fn kill_strongly_updated_origins<'tcx>(
    local_decls: &LocalDecls<'tcx>,
    target: &Place<'tcx>,
    live: &mut Vec<PlaceKey>,
) {
    let deref_count = target
        .projection
        .iter()
        .filter(|p| matches!(p, ProjectionElem::Deref))
        .count();

    // No Deref: strong update is always valid on local variables.
    if deref_count == 0 {
        let target_key = PlaceKey::from_mir_place(target);
        live.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
        return;
    }

    // Single Deref as the first projection: a write through `&mut T` is a
    // strong update (Rust guarantees exclusive access), whereas writes through
    // raw pointers (`*mut T`, `*const T`) are NOT strong updates.
    if deref_count == 1
        && matches!(
            target.projection[0],
            ProjectionElem::Deref
        )
    {
        let ty = local_decls[target.local].ty;
        if matches!(ty.kind(), ty::Ref(_, _, ty::Mutability::Mut)) {
            let target_key = PlaceKey::from_mir_place(target);
            live.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
        }
    }
}

/// True when `prefix` denotes the same place as `place` or one of its parents
/// (same base and `prefix.fields` is a leading segment of `place.fields`).
fn place_key_is_prefix_of(prefix: &PlaceKey, place: &PlaceKey) -> bool {
    prefix.base == place.base
        && prefix.fields.len() <= place.fields.len()
        && place.fields[..prefix.fields.len()] == prefix.fields[..]
}

/// True when `place` reads or writes through a still-live transferred pointer.
fn place_is_raw_access_to_live_origin<'tcx>(place: &Place<'tcx>, live: &[PlaceKey]) -> bool {
    if !place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
    {
        return false;
    }
    let key = PlaceKey::from_mir_place(place);
    live.iter().any(|origin| key.overlaps(origin))
}

/// True when the rvalue dereferences a still-live transferred pointer.
fn rvalue_reads_live_origin<'tcx>(rvalue: &Rvalue<'tcx>, live: &[PlaceKey]) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| place_is_raw_access_to_live_origin(place, live))
}

/// True when the rvalue copies the *value* of a still-live origin (or takes
/// its address), so the assignment target keeps referring to the transferred
/// pointer and must join the live set.
fn rvalue_copies_live_origin_value<'tcx>(rvalue: &Rvalue<'tcx>, live: &[PlaceKey]) -> bool {
    let Some(place) = rvalue_source_place(rvalue) else {
        return false;
    };
    if place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
    {
        return false;
    }
    let key = PlaceKey::from_mir_place(place);
    live.iter().any(|origin| key.overlaps(origin))
}

/// True when a call terminator passes a still-live transferred pointer to
/// another function.
fn terminator_uses_live_origin<'tcx>(kind: &TerminatorKind<'tcx>, live: &[PlaceKey]) -> bool {
    let TerminatorKind::Call { args, .. } = kind else {
        return false;
    };
    args.iter().any(|arg| {
        let Some(place) = (match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            Operand::Constant(_) => None,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => None,
        }) else {
            return false;
        };
        let key = PlaceKey::from_mir_place(place);
        live.iter().any(|origin| key.overlaps(origin))
    })
}

fn expand_origin_aliases(aliases: &HashMap<Local, PlaceKey>, origins: &mut Vec<PlaceKey>) {
    let mut changed = true;
    while changed {
        changed = false;
        for (local, alias) in aliases {
            let local_key = PlaceKey {
                base: PlaceBaseKey::Local(local.as_usize()),
                fields: Vec::new(),
            };

            let related = origins.iter().any(|origin| {
                local_key.overlaps(origin)
                    || origin.overlaps(&local_key)
                    || alias.overlaps(origin)
                    || origin.overlaps(alias)
            });
            if !related {
                continue;
            }

            if !origins.contains(&local_key) {
                origins.push(local_key);
                changed = true;
            }
            if !origins.contains(alias) {
                origins.push(alias.clone());
                changed = true;
            }
        }
    }
}

fn expand_hazard_alias_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    hazard_locals: &mut HashSet<Local>,
) {
    let body = tcx.optimized_mir(caller);
    let mut changed = true;
    while changed {
        changed = false;
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();
                if rvalue_mentions_any_local(rvalue, hazard_locals)
                    && hazard_locals.insert(target.local)
                {
                    changed = true;
                }
            }
        }
    }
}

fn hazard_used_after_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    block: BasicBlock,
    statement_index: usize,
    hazard_locals: &HashSet<Local>,
) -> bool {
    let body = tcx.optimized_mir(caller);
    let data = &body.basic_blocks[block];
    for statement in data.statements.iter().skip(statement_index + 1) {
        if statement_uses_any_local(statement, hazard_locals) {
            return true;
        }
    }
    let terminator = data.terminator();
    if terminator_uses_any_local(&terminator.kind, hazard_locals) {
        return true;
    }
    hazard_used_after_block(tcx, caller, block, hazard_locals)
}

fn hazard_used_after_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    start: BasicBlock,
    hazard_locals: &HashSet<Local>,
) -> bool {
    let body = tcx.optimized_mir(caller);
    let mut seen = HashSet::new();
    let mut stack: Vec<_> = body.basic_blocks[start].terminator().successors().collect();

    while let Some(block) = stack.pop() {
        if !seen.insert(block) {
            continue;
        }
        let data = &body.basic_blocks[block];
        for statement in &data.statements {
            if statement_uses_any_local(statement, hazard_locals) {
                return true;
            }
        }
        let terminator = data.terminator();
        if terminator_uses_any_local(&terminator.kind, hazard_locals) {
            return true;
        }
        stack.extend(terminator.successors());
    }

    false
}

fn statement_uses_any_local<'tcx>(
    statement: &rustc_middle::mir::Statement<'tcx>,
    locals: &HashSet<Local>,
) -> bool {
    let StatementKind::Assign(assign) = &statement.kind else {
        return false;
    };
    let (target, rvalue) = assign.as_ref();
    locals.contains(&target.local) || rvalue_mentions_any_local(rvalue, locals)
}

fn terminator_uses_any_local<'tcx>(
    terminator: &TerminatorKind<'tcx>,
    locals: &HashSet<Local>,
) -> bool {
    match terminator {
        TerminatorKind::Call { args, .. } => args.iter().any(|arg| match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => locals.contains(&place.local),
            Operand::Constant(_) => false,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => false,
        }),
        TerminatorKind::SwitchInt { discr, .. } | TerminatorKind::Assert { cond: discr, .. } => {
            match discr {
                Operand::Copy(place) | Operand::Move(place) => locals.contains(&place.local),
                Operand::Constant(_) => false,
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => false,
            }
        }
        TerminatorKind::Drop { place, .. } => locals.contains(&place.local),
        _ => false,
    }
}

fn rvalue_mentions_any_local<'tcx>(rvalue: &Rvalue<'tcx>, locals: &HashSet<Local>) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| locals.contains(&place.local))
}

fn blocks_reachable_after_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
) -> HashSet<BasicBlock> {
    let body = tcx.optimized_mir(caller);
    let mut starts = Vec::new();
    if let TerminatorKind::Call { target, .. } = &body.basic_blocks[call_block].terminator().kind
        && let Some(target) = target
    {
        starts.push(*target);
    }

    let mut seen = HashSet::new();
    let mut stack = starts;
    while let Some(block) = stack.pop() {
        if !seen.insert(block) {
            continue;
        }
        let terminator = body.basic_blocks[block].terminator();
        for successor in terminator.successors() {
            stack.push(successor);
        }
    }
    seen
}

fn raw_access_conflicts(kind: HazardKind, access: RawAccessKind) -> bool {
    match kind {
        HazardKind::SharedView => access == RawAccessKind::Write,
        HazardKind::UniqueView => true,
    }
}

pub(super) fn self_field_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    place: &PlaceKey,
) -> Option<SelfFieldOrigin> {
    let PlaceBaseKey::Local(local) = place.base else {
        return None;
    };
    let resolved = resolve_self_field_origin(tcx, caller, local, &place.fields)?;
    Some(SelfFieldOrigin {
        struct_def_id: resolved.struct_def_id,
        field_index: resolved.field_index,
        field_name: resolved.field_name,
    })
}

/// Extract the self-borrow mutability from a method signature.
/// Returns `None` for self-by-value, `Some(Mut)` for `&mut self`,
/// `Some(Not)` for `&self`.
fn self_borrow_mutability<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<ty::Mutability> {
    let body = tcx.optimized_mir(def_id);
    if body.arg_count == 0 {
        return None;
    }
    match body.local_decls[Local::from_usize(1)].ty.kind() {
        TyKind::Ref(_, _, m) => Some(*m),
        _ => None,
    }
}

pub(super) fn escaped_self_field_violation<'tcx>(
    tcx: TyCtxt<'tcx>,
    current: DefId,
    origin: &SelfFieldOrigin,
) -> Option<String> {
    if public_raw_field(tcx, origin) {
        return Some(format!(
            "returned view escapes while raw field `{}` is public",
            origin.field_name
        ));
    }

    let current_self = self_borrow_mutability(tcx, current);

    for impl_def_id in impls_for_struct(tcx, origin.struct_def_id) {
        for item in tcx.associated_item_def_ids(impl_def_id) {
            if *item == current {
                continue;
            }
            if !matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn) {
                continue;
            }
            if check_safety(tcx, *item) == Safety::Unsafe {
                continue;
            }
            let Some(assoc) = tcx.opt_associated_item(*item) else {
                continue;
            };
            if !matches!(assoc.kind, AssocKind::Fn { has_self: true, .. }) {
                continue;
            }
            if !tcx.is_mir_available(*item) {
                continue;
            }

            let item_self = self_borrow_mutability(tcx, *item);

            if method_writes_self_field(tcx, *item, origin.field_index) {
                if current_self.is_none() {
                    continue;
                }
                if let (Some(ty::Mutability::Not), Some(ty::Mutability::Mut)) = (current_self, item_self) {
                    continue;
                }
                return Some(format!(
                    "safe method `{}` writes through raw field `{}`",
                    tcx.def_path_str(*item),
                    origin.field_name
                ));
            }
            if method_exposes_self_field(tcx, *item, origin.field_index) {
                // If current takes self by value, the raw field is consumed —
                // no other method can access it afterward.
                if current_self.is_none() {
                    continue;
                }
                // If current takes &self and item takes &mut self, they
                // cannot coexist under Rust's borrow rules — no hazard.
                if let (Some(ty::Mutability::Not), Some(ty::Mutability::Mut)) = (current_self, item_self) {
                    continue;
                }
                // Two &mut self methods also cannot coexist.
                if let (Some(ty::Mutability::Mut), Some(ty::Mutability::Mut)) = (current_self, item_self) {
                    continue;
                }
                return Some(format!(
                    "safe method `{}` exposes raw field `{}`",
                    tcx.def_path_str(*item),
                    origin.field_name
                ));
            }
        }
    }

    None
}

fn impls_for_struct(tcx: TyCtxt<'_>, struct_def_id: DefId) -> Vec<DefId> {
    let mut impls = tcx
        .inherent_impls(struct_def_id)
        .iter()
        .copied()
        .collect::<Vec<_>>();

    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::Impl(impl_details) = &item.kind else {
            continue;
        };
        let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) =
            &impl_details.self_ty.kind
        else {
            continue;
        };
        let rustc_hir::def::Res::Def(_, def_id) = path.res else {
            continue;
        };
        if def_id != struct_def_id {
            continue;
        }
        let impl_def_id = item_id.owner_id.to_def_id();
        if !impls.contains(&impl_def_id) {
            impls.push(impl_def_id);
        }
    }

    impls
}

fn public_raw_field<'tcx>(tcx: TyCtxt<'tcx>, origin: &SelfFieldOrigin) -> bool {
    let adt = tcx.adt_def(origin.struct_def_id);
    let Some(field) = adt.all_fields().nth(origin.field_index) else {
        return false;
    };
    if !field.vis.is_public() {
        return false;
    }
    let args = ty::GenericArgs::identity_for_item(tcx, origin.struct_def_id);
    #[cfg(not(rapx_rustc_ge_198))]
    let field_ty = field.ty(tcx, args);
    #[cfg(rapx_rustc_ge_198)]
    let field_ty = field.ty(tcx, args).skip_norm_wip();
    matches!(field_ty.kind(), TyKind::RawPtr(..))
}

fn method_writes_self_field<'tcx>(tcx: TyCtxt<'tcx>, method: DefId, field_index: usize) -> bool {
    let body = tcx.optimized_mir(method);
    let aliases = collect_place_aliases(tcx, method);
    let origin = self_field_key(field_index);

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, _) = assign.as_ref();
            if place_is_raw_access_to_origin(target, &origin, &aliases, &body.local_decls)
                || place_raw_accesses_self_field(tcx, method, target, field_index)
            {
                return true;
            }
        }

        let Some(terminator) = &block.terminator else {
            continue;
        };
        if terminator_writes_origin(tcx, method, &terminator.kind, &origin, &aliases) {
            return true;
        }
    }

    false
}

fn place_raw_accesses_self_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    method: DefId,
    place: &Place<'tcx>,
    field_index: usize,
) -> bool {
    if !place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
    {
        return false;
    }
    local_traces_to_self_field(tcx, method, place.local, field_index, &mut HashSet::new())
}

fn local_traces_to_self_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    method: DefId,
    local: Local,
    field_index: usize,
    seen: &mut HashSet<Local>,
) -> bool {
    if !seen.insert(local) {
        return false;
    }
    let body = tcx.optimized_mir(method);
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local != local {
                continue;
            }
            let Some(source) = rvalue_source_place(rvalue) else {
                continue;
            };
            let source_key = PlaceKey::from_mir_place(source);
            if source_key.base == PlaceBaseKey::Local(1)
                && source_key.fields.first() == Some(&field_index)
            {
                return true;
            }
            if source_key.fields.is_empty()
                && local_traces_to_self_field(tcx, method, source.local, field_index, seen)
            {
                return true;
            }
        }
    }
    false
}

fn method_exposes_self_field<'tcx>(tcx: TyCtxt<'tcx>, method: DefId, field_index: usize) -> bool {
    let body = tcx.optimized_mir(method);

    // If the method takes `self` by value, the raw field is consumed —
    // it cannot be used after the method returns, so exposing a view is safe.
    if body.arg_count >= 1 {
        let self_ty = body.local_decls[Local::from_usize(1)].ty;
        if !matches!(self_ty.kind(), TyKind::Ref(_, _, _)) {
            return false;
        }
    }

    // Only flag methods whose return type IS a reference or raw pointer —
    // scalar types (usize, bool, etc.) computed from the raw field cannot
    // create aliasing hazards.
    let ret_ty = body.local_decls[Local::from_usize(0)].ty;
    if !type_contains_ref_or_ptr(tcx, ret_ty) {
        return false;
    }

    let aliases = collect_place_aliases(tcx, method);
    let origin = self_field_key(field_index);

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local.as_usize() == 0 && rvalue_mentions_origin(rvalue, &origin, &aliases) {
                return true;
            }
        }
    }

    false
}

/// Recursively check whether a type is/contains a reference (`&T`, `&mut T`)
/// or a raw pointer (`*const T`, `*mut T`).
fn type_contains_ref_or_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Ref(_, _, _) | TyKind::RawPtr(_, _) => true,
        TyKind::Tuple(elems) => elems.iter().any(|t| type_contains_ref_or_ptr(tcx, t)),
        TyKind::Adt(def, args) => {
            if args.iter().any(|arg| {
                if let Some(t) = arg.as_type() {
                    type_contains_ref_or_ptr(tcx, t)
                } else {
                    false
                }
            }) {
                return true;
            }
            let adt = tcx.adt_def(def.did());
            adt.all_fields().any(|field| {
                #[cfg(not(rapx_rustc_ge_198))]
                let field_ty = field.ty(tcx, args);
                #[cfg(rapx_rustc_ge_198)]
                let field_ty = field.ty(tcx, args).skip_norm_wip();
                type_contains_ref_or_ptr(tcx, field_ty)
            })
        }
        _ => false,
    }
}

fn escaped_nonnull_as_mut_violation<'tcx>(
    tcx: TyCtxt<'tcx>,
    current: DefId,
    origin: &SelfFieldOrigin,
) -> Option<String> {
    for impl_def_id in impls_for_struct(tcx, origin.struct_def_id) {
        for item in tcx.associated_item_def_ids(impl_def_id) {
            if *item == current {
                continue;
            }
            if !matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn) {
                continue;
            }
            if check_safety(tcx, *item) == Safety::Unsafe {
                continue;
            }
            let Some(assoc) = tcx.opt_associated_item(*item) else {
                continue;
            };
            if !matches!(assoc.kind, AssocKind::Fn { has_self: true, .. }) {
                continue;
            }
            if !tcx.is_mir_available(*item) {
                continue;
            }

            if method_uses_nonnull_on_self_field(tcx, *item, origin.field_index) {
                return Some(format!(
                    "safe method `{}` creates a NonNull::as_mut reference from field `{}`",
                    tcx.def_path_str(*item),
                    origin.field_name
                ));
            }
        }
    }
    None
}

fn method_uses_nonnull_on_self_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    method: DefId,
    field_index: usize,
) -> bool {
    let body = tcx.optimized_mir(method);
    let origins = collect_local_origins(tcx, method);

    for block in body.basic_blocks.iter() {
        let Some(terminator) = &block.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };
        let callee_name = crate::helpers::mir_utils::call_name(tcx, func);
        if !callee_name.contains("::NonNull::<")
            || (!callee_name.ends_with("::as_ref") && !callee_name.ends_with("::as_mut"))
        {
            continue;
        }
        let Some(arg0) = args.first() else {
            continue;
        };
        let Some(place) = (match &arg0.node {
            Operand::Copy(p) | Operand::Move(p) => Some(p),
            _ => None,
        }) else {
            continue;
        };
        let (plocal, pfields) = resolve_place(place, &origins);
        if plocal == 1 && pfields.first() == Some(&field_index) {
            return true;
        }
    }

    false
}

fn self_field_key(field_index: usize) -> PlaceKey {
    PlaceKey {
        base: PlaceBaseKey::Local(1),
        fields: vec![field_index],
    }
}

fn collect_place_aliases<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> HashMap<Local, PlaceKey> {
    collect_local_origins(tcx, def_id)
        .into_iter()
        .map(|(local, (origin_local, fields))| {
            (Local::from_usize(local), PlaceKey::from_origin(origin_local, fields))
        })
        .collect()
}

fn alias_from_rvalue<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _def_id: DefId,
    rvalue: &Rvalue<'tcx>,
    aliases: &HashMap<Local, PlaceKey>,
) -> Option<PlaceKey> {
    let place = rvalue_source_place(rvalue)?;
    Some(resolve_mir_place(place, aliases))
}

fn resolve_mir_place<'tcx>(
    place: &Place<'tcx>,
    aliases: &HashMap<Local, PlaceKey>,
) -> PlaceKey {
    let key = PlaceKey::from_mir_place(place);
    if !key.fields.is_empty() {
        return key;
    }
    aliases.get(&place.local).cloned().unwrap_or(key)
}

fn place_is_raw_access_to_origin<'tcx>(
    place: &Place<'tcx>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
    local_decls: &LocalDecls<'tcx>,
) -> bool {
    let local = place.local;
    let has_raw_deref = place.projection.iter().any(|projection| {
        if let ProjectionElem::Deref = projection {
            matches!(local_decls[local].ty.kind(), TyKind::RawPtr(_, _))
        } else {
            false
        }
    });
    if !has_raw_deref {
        return false;
    }
    let pointer = aliases
        .get(&place.local)
        .cloned()
        .unwrap_or_else(|| PlaceKey::from_mir_place(place));
    pointer.overlaps(origin)
}

fn place_is_raw_access_to_any_origin<'tcx>(
    place: &Place<'tcx>,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
    local_decls: &LocalDecls<'tcx>,
) -> bool {
    origins
        .iter()
        .any(|origin| place_is_raw_access_to_origin(place, origin, aliases, local_decls))
}

/// True when reading through `rvalue` is actually dereferencing a place
/// whose type is a reference — it's a view re-borrow, not a raw pointer
/// access from outside the view hierarchy.
fn rvalue_reads_like_view<'tcx>(
    rvalue: &Rvalue<'tcx>,
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let Some(place) = rvalue_source_place(rvalue) else { return false; };
    if !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
        return false;
    }
    let pointer = aliases
        .get(&place.local)
        .cloned()
        .unwrap_or_else(|| PlaceKey::from_mir_place(place));
    // The dereferenced local must trace to one of the origins.
    if !origins.iter().any(|origin| pointer.overlaps(origin)) {
        return false;
    }
    // The origin must ultimately be a reference (&T or &mut T) —
    // otherwise the pointer came from an owned allocation (e.g. Vec)
    // and reading through it IS a hazard.
    is_origin_a_reference(tcx, caller, &pointer)
}

fn rvalue_has_hazard_local_base<'tcx>(
    rvalue: &Rvalue<'tcx>,
    hazard_locals: &HashSet<Local>,
) -> bool {
    let Some(place) = rvalue_source_place(rvalue) else {
        return false;
    };
    hazard_locals.contains(&place.local)
}

fn rvalue_reads_any_origin<'tcx>(
    rvalue: &Rvalue<'tcx>,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
    local_decls: &LocalDecls<'tcx>,
) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| place_is_raw_access_to_any_origin(place, origins, aliases, local_decls))
}

fn rvalue_mentions_origin<'tcx>(
    rvalue: &Rvalue<'tcx>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| resolve_mir_place(place, aliases).overlaps(origin))
}

fn terminator_writes_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    _caller: DefId,
    terminator: &TerminatorKind<'tcx>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    if !fn_simulator::is_ptr_write(&name) {
        return false;
    }
    let Some(arg0) = args.first() else {
        return false;
    };
    let Some(place) = (match &arg0.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => None,
    }) else {
        return false;
    };
    resolve_mir_place(place, aliases).overlaps(origin)
}

// Box::from_raw, drop_in_place, and similar ownership-transfer operations
// consume the pointer and deallocate memory — they resolve the alias hazard
// rather than creating a new one.
fn is_ownership_transfer_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &TerminatorKind<'tcx>,
) -> bool {
    let TerminatorKind::Call { func, .. } = terminator else {
        return false;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    name.contains("::from_raw") || name.contains("::drop_in_place")
}

fn terminator_uses_origin<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _caller: DefId,
    terminator: &TerminatorKind<'tcx>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let TerminatorKind::Call { args, .. } = terminator else {
        return false;
    };
    args.iter().any(|arg| {
        let Some(place) = (match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            Operand::Constant(_) => None,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => None,
        }) else {
            return false;
        };
        resolve_mir_place(place, aliases).overlaps(origin)
    })
}

fn terminator_returns_ownership<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &TerminatorKind<'tcx>,
    owner_locals: &HashSet<Local>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    if !is_ownership_return_api(&name) {
        return false;
    }
    args.iter().any(|arg| match &arg.node {
        Operand::Copy(place) | Operand::Move(place) => owner_locals.contains(&place.local),
        Operand::Constant(_) => false,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => false,
    })
}

fn is_ownership_return_api(name: &str) -> bool {
    name.contains("into_raw")
        && (name.contains("boxed")
            || name.contains("Box")
            || name.contains("ffi::c_str")
            || name.contains("CString"))
}

fn vec_owners_for_origins<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> Vec<PlaceKey> {
    find_as_ptr_receivers(tcx, caller, origins, aliases, true)
}

fn terminator_invalidates_vec_owner<'tcx>(
    tcx: TyCtxt<'tcx>,
    _caller: DefId,
    terminator: &TerminatorKind<'tcx>,
    owners: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    if !is_vec_invalidating_method(&name) {
        return false;
    }
    args.iter().any(|arg| {
        let Some(place) = (match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            Operand::Constant(_) => None,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => None,
        }) else {
            return false;
        };
        let arg = resolve_mir_place(place, aliases);
        owners
            .iter()
            .any(|owner| arg.overlaps(owner) || owner.overlaps(&arg))
    })
}

fn is_vec_invalidating_method(name: &str) -> bool {
    (name.contains("Vec") || name.contains("vec::"))
        && (name.contains("::push")
            || name.contains("::reserve")
            || name.contains("::reserve_exact")
            || name.contains("::shrink_to_fit")
            || name.contains("::shrink_to")
            || name.contains("::insert")
            || name.contains("::remove")
            || name.contains("::clear")
            || name.contains("::truncate")
            || name.contains("::set_len"))
}
