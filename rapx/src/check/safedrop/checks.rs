use rustc_span::Span;
use crate::analysis::alias::default::graph::AliasGraph;
use crate::analysis::alias::default::types::ValueKind;
use super::bug_records::*;
use super::drop::*;

// ── public entry points ──

/// Extends `drop_record` to match `graph.values.len()`.
/// For each new index, if the value has a father, copies from the father's
/// drop_record; otherwise creates a false_record.
pub fn sync_drop_record(graph: &AliasGraph, drop_record: &mut Vec<DropRecord>) {
    while drop_record.len() < graph.values.len() {
        let new_idx = drop_record.len();
        let father = graph.values[new_idx].father.clone();
        drop_record.push(if let Some(ref fi) = father {
            DropRecord::from(new_idx, &drop_record[fi.father_value_id])
        } else {
            DropRecord::false_record(new_idx)
        });
    }
}

pub fn clear_drop_info(graph: &AliasGraph, drop_record: &mut Vec<DropRecord>, value_idx: usize) {
    rap_debug!("clear_drop: value_idx = {}", value_idx);
    drop_record[value_idx].clear();
    clear_field_drop(graph, drop_record, value_idx);
    clear_father_drop(graph, drop_record, value_idx);
}

pub fn uaf_check(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    bug_records: &mut BugRecords,
    value_idx: usize,
    bb_idx: usize,
    span: Span,
    is_fncall: bool,
) {
    let local = graph.values[value_idx].local;
    rap_debug!(
        "uaf_check, idx: {:?}, local: {:?}, drop_record: {:?}",
        value_idx,
        local,
        drop_record[value_idx],
    );
    if !graph.values[value_idx].may_drop {
        return;
    }
    if graph.values[value_idx].is_ptr() && !is_fncall {
        return;
    }
    let Some(confidence) = check_drop_status(graph, drop_record, value_idx) else {
        return;
    };
    if bug_records.uaf_bugs.contains_key(&local) {
        return;
    }
    let drop_spot = drop_record[value_idx].drop_spot;
    if let Some(t) = bug_records.try_merge_pair(drop_spot, bb_idx, BugType::UseAfterFree) {
        let bug = make_bug(
            &drop_record[value_idx],
            LocalSpot::new(bb_idx, local),
            span.clone(),
            confidence,
            t,
        );
        rap_warn!("Find a use-after-free bug {:?}; add to records", bug);
        bug_records.uaf_bugs.insert(local, bug);
    }
}

// ── internal helpers ──

pub fn check_drop_status(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    idx: usize,
) -> Option<usize> {
    fetch_drop_info(graph, drop_record, idx);
    let mut fully_dropped = true;
    if !drop_record[idx].is_dropped {
        fully_dropped = false;
        if !drop_record[idx].has_dropped_field {
            return None;
        }
    }
    let kind = graph.values[idx].kind;
    Some(rate_confidence(kind, fully_dropped))
}

fn rate_confidence(kind: ValueKind, fully_dropped: bool) -> usize {
    match (kind, fully_dropped) {
        (ValueKind::SpecialPtr, _) => 0,
        (_, true) => 99,
        (_, false) => 50,
    }
}

pub fn make_bug(
    drop_record: &DropRecord,
    trigger_info: LocalSpot,
    span: Span,
    confidence: usize,
    bug_type: BugType,
) -> TyBug {
    TyBug {
        drop_spot: drop_record.drop_spot,
        trigger_info,
        span,
        confidence,
        bug_type,
    }
}

// ── drop propagation ──

pub fn push_drop_info(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    value_idx: usize,
    drop_spot: LocalSpot,
) {
    push_drop_bottom_up(graph, drop_record, value_idx, drop_spot);
    push_drop_top_down(graph, drop_record, value_idx, drop_spot);
}

fn push_drop_bottom_up(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    value_idx: usize,
    drop_spot: LocalSpot,
) {
    rap_debug!("push_drop_bottom_up: value_idx = {}", value_idx);
    let mut father = graph.values[value_idx].father.clone();
    let mut prop_chain = vec![value_idx];
    while let Some(father_info) = father {
        let father_idx = father_info.father_value_id;
        drop_record[father_idx].has_dropped_field = true;
        if !drop_record[father_idx].is_dropped {
            prop_chain.push(father_idx);
            drop_record[father_idx].prop_chain = prop_chain.clone();
            drop_record[father_idx].drop_spot = drop_spot;
        }
        rap_debug!("{:?}", drop_record[father_idx]);
        father = graph.values[father_idx].father.clone();
    }
}

fn push_drop_top_down(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    value_idx: usize,
    drop_spot: LocalSpot,
) {
    rap_debug!("push_drop_top_down: value_idx = {}", value_idx);
    let mut prop_chain = vec![value_idx];
    for (_field_id, field_value_id) in graph.values[value_idx].fields.clone() {
        if graph.values[field_value_id].kind == ValueKind::Ref {
            continue;
        }
        drop_record[field_value_id] = DropRecord::new(field_value_id, true, drop_spot);
        prop_chain.push(field_value_id);
        drop_record[field_value_id].prop_chain = prop_chain.clone();
        rap_debug!("{:?}", drop_record[field_value_id]);
        push_drop_top_down(graph, drop_record, field_value_id, drop_spot);
    }
}

// ── drop fetching ──

fn fetch_drop_info(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    value_idx: usize,
) {
    fetch_drop_from_bottom(graph, drop_record, value_idx);
    fetch_drop_from_top(graph, drop_record, value_idx);
    fetch_drop_from_alias(graph, drop_record, value_idx);
}

fn fetch_drop_from_bottom(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    value_idx: usize,
) {
    rap_debug!("fetch_drop_from_bottom: value_idx = {}", value_idx);
    for (_field_id, field_value_id) in graph.values[value_idx].fields.clone() {
        rap_debug!("{:?}", drop_record[field_value_id]);
        fetch_drop_from_alias(graph, drop_record, field_value_id);
        if drop_record[field_value_id].is_dropped {
            push_drop_bottom_up(
                graph,
                drop_record,
                field_value_id,
                drop_record[field_value_id].drop_spot,
            );
            rap_debug!("{:?}", drop_record[value_idx]);
            break;
        }
        fetch_drop_from_bottom(graph, drop_record, field_value_id);
    }
}

fn fetch_drop_from_top(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    value_idx: usize,
) {
    rap_debug!("fetch_drop_from_top: value_idx = {}", value_idx);
    let mut father = graph.values[value_idx].father.clone();
    while let Some(father_info) = father {
        let father_idx = father_info.father_value_id;
        fetch_drop_from_alias(graph, drop_record, father_idx);
        if drop_record[father_idx].is_dropped {
            push_drop_top_down(
                graph,
                drop_record,
                father_idx,
                drop_record[father_idx].drop_spot,
            );
            rap_debug!("{:?}", drop_record[value_idx]);
            break;
        }
        father = graph.values[father_idx].father.clone();
    }
}

fn fetch_drop_from_alias(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    value_idx: usize,
) {
    rap_debug!("fetch_drop_from_alias: value_idx = {}", value_idx);
    if let Some(aliases) = get_alias_set(graph, value_idx) {
        for idx in aliases {
            if drop_record[idx].is_dropped {
                drop_record[value_idx] = drop_record[idx].clone();
                drop_record[value_idx].value_index = value_idx;
                drop_record[value_idx].prop_chain.push(value_idx);
            }
        }
    }
}

// ── drop clearing ──

fn clear_father_drop(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    value_idx: usize,
) {
    rap_debug!("clear_drop_father: value_idx = {}", value_idx);
    let mut father = graph.values[value_idx].father.clone();
    while let Some(father_info) = father {
        let father_idx = father_info.father_value_id;
        if !drop_record[father_idx].is_dropped {
            drop_record[father_idx].clear();
        }
        father = graph.values[father_idx].father.clone();
    }
}

fn clear_field_drop(
    graph: &AliasGraph,
    drop_record: &mut Vec<DropRecord>,
    value_idx: usize,
) {
    rap_debug!("clear_field_drop: value_idx = {}", value_idx);
    for (_field_id, field_value_id) in graph.values[value_idx].fields.clone() {
        drop_record[field_value_id].clear();
        clear_field_drop(graph, drop_record, field_value_id);
    }
}

// ── misc ──

fn get_alias_set(graph: &AliasGraph, e: usize) -> Option<Vec<usize>> {
    let idx = graph.find_alias_set(e)?;
    Some(graph.alias_sets[idx].iter().copied().collect())
}
