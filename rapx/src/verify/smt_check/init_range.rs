//! Per-object initialization range simulator.
//!
//! Path extraction unrolls loops into flat paths. The forward verifier records
//! point-wise `KnownInit { elements: 1 }` facts for each `ptr.write(v)` along
//! the path.  This module aggregates those single-write facts by allocation
//! object, resolves each write's offset, and merges adjacent ranges so the SMT
//! checker can discharge `Init(target, T, N)` by simple range-cover arithmetic.

use std::collections::{HashMap, HashSet};

use rustc_middle::mir::BinOp;

use crate::verify::call_summary::CallEffect;
use crate::verify::def_use::{PlaceBaseKey, PlaceKey};
use crate::verify::verifier::{AbstractValue, ForwardVisitResult, StateFact};

use super::common::{InitRange, InitRangeState, SmtTerm, place_label};

/// Aggregates point-wise `KnownInit` facts into per-object init ranges.
pub(crate) struct InitRangeAggregator;

impl InitRangeAggregator {
    /// Consume `ForwardVisitResult` facts and produce per-object init ranges.
    pub fn aggregate<'tcx>(forward: &ForwardVisitResult<'tcx>) -> Vec<InitRangeState> {
        let mut per_object: HashMap<PlaceKey, Vec<(SmtTerm, String, String)>> = HashMap::new();

        let mut visited = HashSet::new();
        for fact in &forward.facts {
            let StateFact::KnownInit {
                place,
                ty_name,
                elements: _,
                reason,
            } = fact
            else {
                continue;
            };

            visited.clear();
            let Some((object, offset)) = resolve_place_offset(place, forward, &mut visited) else {
                continue;
            };

            per_object
                .entry(object)
                .or_default()
                .push((offset, ty_name.clone(), reason.clone()));
        }

        per_object
            .into_iter()
            .map(|(object, writes)| {
                let ranges = merge_writes(writes);
                InitRangeState { object, ranges }
            })
            .collect()
    }
}

// ── offset resolution ───────────────────────────────────────────────────

fn resolve_place_offset<'tcx>(
    place: &PlaceKey,
    forward: &ForwardVisitResult<'tcx>,
    visited: &mut HashSet<PlaceKey>,
) -> Option<(PlaceKey, SmtTerm)> {
    if !visited.insert(place.clone()) {
        return None;
    }
    let value = resolve_value_for_place(place, forward)?;
    resolve_value_offset(&value, forward, visited)
}

fn resolve_value_for_place<'tcx>(
    place: &PlaceKey,
    forward: &ForwardVisitResult<'tcx>,
) -> Option<AbstractValue<'tcx>> {
    let local = place.local()?;
    let mut value = forward.values.get(&local).cloned();
    if value.is_none() {
        if let Some(def) =
            forward.latest_value_definition_before(local, forward.value_definitions.len())
        {
            value = Some(def.value.clone());
        }
    }
    value
}

fn resolve_value_offset<'tcx>(
    value: &AbstractValue<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    visited: &mut HashSet<PlaceKey>,
) -> Option<(PlaceKey, SmtTerm)> {
    let resolved = unwrap_cast_chain(value, forward, 0, visited);
    match &resolved {
        AbstractValue::CallResult(call) => {
            resolve_callresult_offset(call, forward, visited)
        }
        AbstractValue::Ref(place) | AbstractValue::RawPtr(place) => {
            if !visited.insert(place.clone()) { return None; }
            let object = resolve_object_for_place(place, forward);
            Some((object, SmtTerm::Const(0)))
        }
        AbstractValue::Place(place) => {
            if !visited.insert(place.clone()) { return None; }
            let object = resolve_object_for_place(place, forward);
            Some((object, SmtTerm::Const(0)))
        }
        _ => None,
    }
}

fn unwrap_cast_chain<'tcx>(
    value: &AbstractValue<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    depth: usize,
    visited: &mut HashSet<PlaceKey>,
) -> AbstractValue<'tcx> {
    if depth > 8 {
        return value.clone();
    }
    match value {
        AbstractValue::Cast(inner, _) => {
            unwrap_cast_chain(inner, forward, depth + 1, visited)
        }
        AbstractValue::Place(place) => {
            if !visited.insert(place.clone()) {
                return value.clone();
            }
            if let Some(v) = resolve_value_for_place(place, forward) {
                unwrap_cast_chain(&v, forward, depth + 1, visited)
            } else {
                value.clone()
            }
        }
        _ => value.clone(),
    }
}

fn resolve_callresult_offset<'tcx>(
    call: &crate::verify::verifier::CallSummary<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    visited: &mut HashSet<PlaceKey>,
) -> Option<(PlaceKey, SmtTerm)> {
    let ptr_add_effect = call.effects.iter().find_map(|e| match e {
        CallEffect::ReturnPointerAdd {
            base_arg,
            offset_arg,
            ..
        } => Some((*base_arg, *offset_arg)),
        CallEffect::ReturnPointerSub {
            base_arg,
            offset_arg,
            ..
        } => Some((*base_arg, *offset_arg)),
        _ => None,
    });
    if let Some((base_arg, offset_arg)) = ptr_add_effect {
        let base_val = call.args.get(base_arg)?;
        let object = resolve_value_to_object(base_val, forward, visited)?;
        let offset = resolve_arg_to_smt_term(offset_arg, call, forward);
        return Some((object, offset));
    }

    let alias_arg = call.effects.iter().find_map(|e| match e {
        CallEffect::ReturnAliasArg { arg } | CallEffect::ReturnPointerFromArg { arg } => Some(*arg),
        _ => None,
    });
    if let Some(arg_idx) = alias_arg {
        let base_val = call.args.get(arg_idx)?;
        let object = resolve_value_to_object(base_val, forward, visited)?;
        return Some((object, SmtTerm::Const(0)));
    }

    let owns_arg = call.effects.iter().find_map(|e| match e {
        CallEffect::OwnsInitMemory { arg } => Some(*arg),
        _ => None,
    });
    if let Some(arg_idx) = owns_arg {
        let base_val = call.args.get(arg_idx)?;
        let object = resolve_value_to_object(base_val, forward, visited)?;
        return Some((object, SmtTerm::Const(0)));
    }

    None
}

fn resolve_value_to_object<'tcx>(
    value: &AbstractValue<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    visited: &mut HashSet<PlaceKey>,
) -> Option<PlaceKey> {
    let resolved = unwrap_cast_chain(value, forward, 0, visited);
    match &resolved {
        AbstractValue::Ref(place) | AbstractValue::RawPtr(place) => {
            if !visited.insert(place.clone()) { return None; }
            Some(resolve_object_for_place(place, forward))
        }
        AbstractValue::Place(place) => {
            if !visited.insert(place.clone()) { return None; }
            Some(resolve_object_for_place(place, forward))
        }
        AbstractValue::CallResult(call) => {
            let alias_arg = call.effects.iter().find_map(|e| match e {
                CallEffect::ReturnAliasArg { arg }
                | CallEffect::ReturnPointerFromArg { arg } => Some(*arg),
                _ => None,
            })?;
            let base_val = call.args.get(alias_arg)?;
            resolve_value_to_object(base_val, forward, visited)
        }
        _ => None,
    }
}

fn resolve_object_for_place(place: &PlaceKey, forward: &ForwardVisitResult) -> PlaceKey {
    let mut resolved = forward.pts_graph.resolve_place(place);
    resolved.fields.clear();
    resolved
}

fn resolve_arg_to_smt_term<'tcx>(
    arg_idx: usize,
    call: &crate::verify::verifier::CallSummary<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtTerm {
    let Some(arg_val) = call.args.get(arg_idx) else {
        return SmtTerm::Const(0);
    };
    match arg_val {
        AbstractValue::ConstInt(v) => SmtTerm::Const(u64::try_from(*v).unwrap_or(0)),
        AbstractValue::Place(place) => SmtTerm::Place(place.clone()),
        AbstractValue::ConstParam(name) => SmtTerm::ConstParam(name.clone()),
        AbstractValue::Binary(BinOp::Add, lhs, rhs)
        | AbstractValue::Binary(BinOp::AddWithOverflow, lhs, rhs) => {
            let l = resolve_arg_to_smt_term_av(lhs, forward);
            let r = resolve_arg_to_smt_term_av(rhs, forward);
            SmtTerm::Add(Box::new(l), Box::new(r))
        }
        AbstractValue::Binary(BinOp::Sub, lhs, rhs)
        | AbstractValue::Binary(BinOp::SubWithOverflow, lhs, rhs) => {
            let l = resolve_arg_to_smt_term_av(lhs, forward);
            let r = resolve_arg_to_smt_term_av(rhs, forward);
            SmtTerm::Sub(Box::new(l), Box::new(r))
        }
        AbstractValue::Binary(BinOp::Mul, lhs, rhs)
        | AbstractValue::Binary(BinOp::MulWithOverflow, lhs, rhs) => {
            let l = resolve_arg_to_smt_term_av(lhs, forward);
            let r = resolve_arg_to_smt_term_av(rhs, forward);
            SmtTerm::Mul(Box::new(l), Box::new(r))
        }
        _ => SmtTerm::Value(place_label(&PlaceKey {
            base: PlaceBaseKey::Local(0),
            fields: vec![],
        })),
    }
}

fn resolve_arg_to_smt_term_av<'tcx>(
    value: &AbstractValue<'tcx>,
    _forward: &ForwardVisitResult<'tcx>,
) -> SmtTerm {
    match value {
        AbstractValue::ConstInt(v) => SmtTerm::Const(u64::try_from(*v).unwrap_or(0)),
        AbstractValue::Place(place) => SmtTerm::Place(place.clone()),
        AbstractValue::ConstParam(name) => SmtTerm::ConstParam(name.clone()),
        _ => SmtTerm::Const(0),
    }
}

// ── range merging ───────────────────────────────────────────────────────

fn cmp_smt_term(a: &SmtTerm, b: &SmtTerm) -> std::cmp::Ordering {
    match (a, b) {
        (SmtTerm::Const(va), SmtTerm::Const(vb)) => va.cmp(vb),
        (SmtTerm::Const(_), _) => std::cmp::Ordering::Less,
        (_, SmtTerm::Const(_)) => std::cmp::Ordering::Greater,
        _ => std::cmp::Ordering::Equal,
    }
}

fn can_merge_range(prev_end: &SmtTerm, next_start: &SmtTerm) -> bool {
    match (prev_end, next_start) {
        (SmtTerm::Const(e), SmtTerm::Const(s)) => e >= s,
        _ => false,
    }
}

fn advance_one(offset: &SmtTerm) -> SmtTerm {
    match offset {
        SmtTerm::Const(n) => SmtTerm::Const(n + 1),
        other => SmtTerm::Add(Box::new(other.clone()), Box::new(SmtTerm::Const(1))),
    }
}

fn merge_writes(mut writes: Vec<(SmtTerm, String, String)>) -> Vec<InitRange> {
    writes.sort_by(|(a, _, _), (b, _, _)| cmp_smt_term(a, b));
    let mut ranges: Vec<InitRange> = Vec::new();
    for (offset, ty_name, reason) in writes {
        let end = advance_one(&offset);
        let can_merge = ranges
            .last()
            .map_or(false, |last| can_merge_range(&last.end, &offset));
        if can_merge {
            let last = ranges.last_mut().unwrap();
            last.end = end;
        } else {
            ranges.push(InitRange {
                start: offset,
                end,
                ty_name,
                reason,
            });
        }
    }
    ranges
}
