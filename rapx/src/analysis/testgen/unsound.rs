use crate::analysis::core::api_dependency::ApiDependencyGraph;
use crate::analysis::core::dataflow::default::DataFlowAnalyzer;
use crate::analysis::core::dataflow::{DataFlowGraph, EdgeOp};
use crate::analysis::testgen::chain::{ChainScheduler, ChainStrategy, HazardTemporalPlan};
use crate::analysis::testgen::context::{
    ApiCall, InputHint, NumericHint, Stmt, StmtKind, Var, DUMMY_INPUT_VAR,
};
use crate::analysis::testgen::context_builder::ContextBuilder;
use crate::analysis::testgen::contract::{PrimitiveSpKind, SafetyContractDb, SafetyPredicate};
use crate::analysis::testgen::coverage::{
    def_id_str, sp_family_name, sp_name, CaseMetadata, CaseTargetRecord, CcagEdgeRecord, CcagFile,
    CcagNodeRecord, ContractInstanceRecord, ContractInstancesFile, TESTGEN_ARTIFACT_SCHEMA_VERSION,
};
use crate::analysis::testgen::guide::{
    ContractGenericPreference, ContractTarget, FuzzGuide, GuidedAction,
};
use crate::analysis::testgen::utils;
use crate::analysis::testgen::value_plan::{direct_numeric_hint_for_predicate, TypeSizeEnv};
use crate::analysis::utils::fn_info::{get_adt_def_id_by_adt_method, get_cleaned_def_path_name};
use crate::rap_info;
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_hir::{BodyOwnerKind, LangItem};
use rustc_middle::mir::{
    Const, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt, TyKind};
use rustc_span::{FileName, FileNameDisplayPreference};
use rustc_type_ir::{FloatTy, IntTy, UintTy};
use serde::Deserialize;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::env;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
enum PlaceRoot {
    Return,
    Receiver,
    Param(usize),
    Local(usize),
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
struct SymbolicPlace {
    root: PlaceRoot,
    fields: Vec<usize>,
}

impl SymbolicPlace {
    fn is_receiver_field(&self) -> bool {
        matches!(self.root, PlaceRoot::Receiver) && !self.fields.is_empty()
    }

    fn is_param(&self) -> Option<usize> {
        match self.root {
            PlaceRoot::Param(idx) => Some(idx),
            _ => None,
        }
    }

    fn appended(&self, fields: &[usize]) -> Self {
        let mut place = self.clone();
        place.fields.extend_from_slice(fields);
        place
    }

    fn is_prefix_of(&self, other: &SymbolicPlace) -> bool {
        self.root == other.root
            && self.fields.len() <= other.fields.len()
            && other.fields.starts_with(&self.fields)
    }

    fn pretty(&self) -> String {
        let root = match self.root {
            PlaceRoot::Return => "return".to_owned(),
            PlaceRoot::Receiver => "self".to_owned(),
            PlaceRoot::Param(idx) => format!("arg{idx}"),
            PlaceRoot::Local(idx) => format!("local{idx}"),
        };
        if self.fields.is_empty() {
            root
        } else {
            format!(
                "{}.{}",
                root,
                self.fields.iter().map(|field| field.to_string()).join(".")
            )
        }
    }
}

#[derive(Debug, Clone, Copy, Deserialize, Eq, Hash, PartialEq)]
#[serde(rename_all = "snake_case")]
#[allow(dead_code)]
enum ContractUsage {
    #[serde(alias = "precond")]
    Precondition,
    Hazard,
    #[serde(alias = "optional")]
    Option,
    Unknown,
}

impl ContractUsage {
    fn name(self) -> &'static str {
        match self {
            Self::Precondition => "precondition",
            Self::Hazard => "hazard",
            Self::Option => "option",
            Self::Unknown => "unknown",
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum NumericPreconditionKind {
    LessThanLen,
    NonZero,
    PowerOfTwo,
    UnicodeScalar,
    OffsetInAllocation,
    Expression,
}

impl NumericPreconditionKind {
    fn invalid_hint(self, reason: impl Into<String>) -> InputHint {
        match self {
            Self::LessThanLen => InputHint::invalid_index(reason),
            Self::NonZero | Self::PowerOfTwo => InputHint::invalid_align(reason),
            Self::UnicodeScalar => InputHint::invalid_unicode_scalar(reason),
            Self::OffsetInAllocation => InputHint::negative_offset(reason),
            Self::Expression => InputHint::numeric(
                reason,
                vec![
                    NumericHint::Zero,
                    NumericHint::Literal(4),
                    NumericHint::Literal(1024),
                ],
            ),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::LessThanLen => "lt_len",
            Self::NonZero => "non_zero",
            Self::PowerOfTwo => "power_of_two",
            Self::UnicodeScalar => "unicode_scalar",
            Self::OffsetInAllocation => "offset_in_allocation",
            Self::Expression => "expression",
        }
    }

    fn sp_kind(self) -> PrimitiveSpKind {
        match self {
            Self::LessThanLen | Self::OffsetInAllocation => PrimitiveSpKind::InBound,
            Self::NonZero | Self::PowerOfTwo => PrimitiveSpKind::ValidNum,
            Self::UnicodeScalar => PrimitiveSpKind::ValidString,
            Self::Expression => PrimitiveSpKind::ValidNum,
        }
    }
}

#[derive(Debug, Clone)]
struct ContractInstance {
    sink_fn: DefId,
    adt_def: Option<DefId>,
    sink_self_ty: Option<String>,
    sink_signature: String,
    sink_requires_monomorphization: bool,
    std_fn: DefId,
    std_fn_name: String,
    sp: PrimitiveSpKind,
    raw_tag: String,
    symbolic_args: Vec<SymbolicPlace>,
    usage: ContractUsage,
    numeric_kind: Option<NumericPreconditionKind>,
    binding_role: Option<String>,
}

impl ContractInstance {
    fn sensitive_place(&self) -> Option<&SymbolicPlace> {
        self.symbolic_args.first()
    }

    fn invalid_hint(&self, reason: impl Into<String>) -> Option<InputHint> {
        let reason = reason.into();
        if let Some(kind) = self.numeric_kind {
            if matches!(kind, NumericPreconditionKind::Expression) {
                if let Some(hints) = numeric_hints_for_expression_predicate(&self.raw_tag) {
                    return Some(InputHint::numeric(reason, hints));
                }
            }
            return Some(kind.invalid_hint(reason));
        }

        match self.sp {
            PrimitiveSpKind::InBound => Some(InputHint::invalid_index(reason)),
            PrimitiveSpKind::Align | PrimitiveSpKind::DoubleAlign => {
                Some(InputHint::misaligned_ptr(reason))
            }
            PrimitiveSpKind::Size
            | PrimitiveSpKind::NonZeroSize
            | PrimitiveSpKind::Layout
            | PrimitiveSpKind::ValidNum => Some(InputHint::invalid_align(reason)),
            PrimitiveSpKind::NonNull => Some(InputHint::null_ptr(reason)),
            PrimitiveSpKind::Null => Some(InputHint::dangling_ptr(reason)),
            PrimitiveSpKind::Allocated
            | PrimitiveSpKind::Alive
            | PrimitiveSpKind::NotOwned
            | PrimitiveSpKind::ValidPtr
            | PrimitiveSpKind::ValidPtr2Ref
            | PrimitiveSpKind::ValidSlice => Some(InputHint::dangling_ptr(reason)),
            PrimitiveSpKind::ValidString => Some(InputHint::invalid_utf8(reason)),
            PrimitiveSpKind::ValidCStr => Some(InputHint::invalid_cstr(reason)),
            PrimitiveSpKind::Init => Some(InputHint::uninit_value(reason)),
            PrimitiveSpKind::Unwrap => {
                if self.std_fn_name.contains("unwrap_err") {
                    Some(InputHint::err_variant(reason))
                } else {
                    Some(InputHint::none_variant(reason))
                }
            }
            PrimitiveSpKind::NonOverlap | PrimitiveSpKind::Alias => {
                Some(InputHint::overlapping_range(reason))
            }
            _ => None,
        }
    }

    fn args_display(&self, tcx: TyCtxt<'_>) -> String {
        self.symbolic_args
            .iter()
            .map(|place| symbolic_place_display(tcx, self.adt_def, place))
            .join(", ")
    }
}

#[derive(Debug, Clone, Copy)]
enum EffectValue {
    Param(usize),
    Const(i128),
    Unknown,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
enum EffectKind {
    WriteField {
        field: SymbolicPlace,
        value: EffectValue,
        inputs: Vec<SymbolicPlace>,
    },
    InvalidateUtf8 {
        place: SymbolicPlace,
    },
    FreeAllocation {
        place: SymbolicPlace,
    },
    CreateAlias {
        lhs: SymbolicPlace,
        rhs: SymbolicPlace,
    },
    DropSource {
        place: SymbolicPlace,
    },
    SetLen {
        place: SymbolicPlace,
        value: EffectValue,
    },
    AssumeInit {
        place: SymbolicPlace,
    },
    ConstructAdt {
        output: SymbolicPlace,
        inputs: Vec<SymbolicPlace>,
    },
}

#[derive(Debug, Clone, Copy)]
enum EffectConfidence {
    Exact,
    Flow,
    Approximate,
}

impl EffectConfidence {
    fn name(self) -> &'static str {
        match self {
            Self::Exact => "exact",
            Self::Flow => "flow",
            Self::Approximate => "approximate",
        }
    }
}

impl EffectKind {
    fn primary_place(&self) -> &SymbolicPlace {
        match self {
            Self::WriteField { field, .. } => field,
            Self::InvalidateUtf8 { place }
            | Self::FreeAllocation { place }
            | Self::DropSource { place }
            | Self::SetLen { place, .. }
            | Self::AssumeInit { place } => place,
            Self::CreateAlias { lhs, .. } => lhs,
            Self::ConstructAdt { output, .. } => output,
        }
    }

    fn value(&self) -> Option<EffectValue> {
        match self {
            Self::WriteField { value, .. } | Self::SetLen { value, .. } => Some(*value),
            _ => None,
        }
    }

    fn input_places(&self) -> &[SymbolicPlace] {
        match self {
            Self::WriteField { inputs, .. } | Self::ConstructAdt { inputs, .. } => inputs,
            _ => &[],
        }
    }

    fn name(&self) -> &'static str {
        match self {
            Self::WriteField { .. } => "WriteField",
            Self::InvalidateUtf8 { .. } => "InvalidateUtf8",
            Self::FreeAllocation { .. } => "FreeAllocation",
            Self::CreateAlias { .. } => "CreateAlias",
            Self::DropSource { .. } => "DropSource",
            Self::SetLen { .. } => "SetLen",
            Self::AssumeInit { .. } => "AssumeInit",
            Self::ConstructAdt { .. } => "ConstructAdt",
        }
    }
}

#[derive(Debug, Clone)]
struct ContractEffect {
    fn_did: DefId,
    adt_def: Option<DefId>,
    kind: EffectKind,
    confidence: EffectConfidence,
}

#[derive(Debug, Clone)]
struct ConflictPair {
    contract_id: usize,
    producer_fn: DefId,
    sink_fn: DefId,
    place: SymbolicPlace,
    sp: PrimitiveSpKind,
    effect_kind: &'static str,
    effect_confidence: &'static str,
    hint_param: Option<usize>,
    hint: Option<InputHint>,
    reason: String,
}

#[derive(Debug, Clone)]
struct DirectSinkHint {
    contract_id: usize,
    sink_fn: DefId,
    param_idx: usize,
    hint: InputHint,
    reason: String,
}

#[derive(Debug, Clone)]
struct PublicFieldTarget {
    contract_id: usize,
    sink_fn: DefId,
    adt_def: DefId,
    field_path: Vec<usize>,
    field_name: String,
    place: SymbolicPlace,
    sp: PrimitiveSpKind,
    hint: Option<InputHint>,
    reason: String,
}

#[derive(Debug, Clone)]
struct HazardTarget {
    contract_id: usize,
    sink_fn: DefId,
    post_fn: DefId,
    place: SymbolicPlace,
    sp: PrimitiveSpKind,
    effect_kind: &'static str,
    effect_confidence: &'static str,
    reason: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum StdContractBinding {
    LtLen {
        value_arg: usize,
        container_arg: usize,
        usage: Option<ContractUsage>,
    },
    NonZero {
        arg: usize,
        usage: Option<ContractUsage>,
    },
    PowerOfTwo {
        arg: usize,
        usage: Option<ContractUsage>,
    },
    UnicodeScalar {
        arg: usize,
        usage: Option<ContractUsage>,
    },
    OffsetInAlloc {
        offset_arg: usize,
        ptr_arg: usize,
        usage: Option<ContractUsage>,
    },
    Arg {
        arg: usize,
        sp: Option<String>,
        role: Option<String>,
        usage: Option<ContractUsage>,
    },
    Args {
        args: Vec<usize>,
        sp: Option<String>,
        role: Option<String>,
        usage: Option<ContractUsage>,
    },
    Predicate {
        predicate: SafetyPredicate,
        role: Option<String>,
        usage: Option<ContractUsage>,
    },
    NoArgs {
        sp: Option<String>,
        usage: Option<ContractUsage>,
    },
}

#[derive(Debug, Clone)]
struct BindingContractSpec {
    raw_tag: String,
    sp: PrimitiveSpKind,
    usage: ContractUsage,
}

impl StdContractBinding {
    fn usage(&self) -> ContractUsage {
        let explicit = match self {
            Self::LtLen { usage, .. }
            | Self::NonZero { usage, .. }
            | Self::PowerOfTwo { usage, .. }
            | Self::UnicodeScalar { usage, .. }
            | Self::OffsetInAlloc { usage, .. }
            | Self::Arg { usage, .. }
            | Self::Args { usage, .. }
            | Self::Predicate { usage, .. }
            | Self::NoArgs { usage, .. } => *usage,
        };
        explicit.unwrap_or_else(|| {
            self.binding_sp()
                .map(|sp| default_contract_usage_for_sp(&sp))
                .unwrap_or(ContractUsage::Precondition)
        })
    }

    fn binding_sp(&self) -> Option<PrimitiveSpKind> {
        match self {
            Self::Predicate { predicate, .. } => Some(predicate.kind().clone()),
            Self::LtLen { .. } | Self::OffsetInAlloc { .. } => Some(PrimitiveSpKind::InBound),
            Self::NonZero { .. } | Self::PowerOfTwo { .. } => Some(PrimitiveSpKind::ValidNum),
            Self::UnicodeScalar { .. } => Some(PrimitiveSpKind::ValidString),
            Self::Arg {
                sp: Some(raw_tag), ..
            }
            | Self::Args {
                sp: Some(raw_tag), ..
            }
            | Self::NoArgs {
                sp: Some(raw_tag), ..
            } => Some(PrimitiveSpKind::from_tag(raw_tag)),
            Self::Arg { sp: None, .. }
            | Self::Args { sp: None, .. }
            | Self::NoArgs { sp: None, .. } => None,
        }
    }

    fn numeric_kind(&self) -> Option<NumericPreconditionKind> {
        match self {
            Self::LtLen { .. } => Some(NumericPreconditionKind::LessThanLen),
            Self::NonZero { .. } => Some(NumericPreconditionKind::NonZero),
            Self::PowerOfTwo { .. } => Some(NumericPreconditionKind::PowerOfTwo),
            Self::UnicodeScalar { .. } => Some(NumericPreconditionKind::UnicodeScalar),
            Self::OffsetInAlloc { .. } => Some(NumericPreconditionKind::OffsetInAllocation),
            Self::Predicate { predicate, .. } if predicate.kind() == &PrimitiveSpKind::ValidNum => {
                Some(NumericPreconditionKind::Expression)
            }
            Self::Arg { .. } | Self::Args { .. } | Self::Predicate { .. } | Self::NoArgs { .. } => {
                None
            }
        }
    }

    fn matches_sp(&self, sp: &PrimitiveSpKind) -> bool {
        if let Self::Predicate { predicate, .. } = self {
            return predicate.kind() == sp;
        }

        if let Some(kind) = self.numeric_kind() {
            return kind.sp_kind() == *sp;
        }

        match self {
            Self::Arg {
                sp: Some(raw_tag), ..
            }
            | Self::Args {
                sp: Some(raw_tag), ..
            }
            | Self::NoArgs {
                sp: Some(raw_tag), ..
            } => PrimitiveSpKind::from_tag(raw_tag) == *sp,
            Self::Arg { sp: None, .. }
            | Self::Args { sp: None, .. }
            | Self::NoArgs { sp: None, .. } => true,
            _ => false,
        }
    }

    fn role(&self) -> Option<&str> {
        match self {
            Self::Arg { role, .. } | Self::Args { role, .. } | Self::Predicate { role, .. } => {
                role.as_deref()
            }
            _ => None,
        }
    }

    fn arg_indices(&self) -> Vec<usize> {
        match self {
            Self::LtLen {
                value_arg,
                container_arg,
                ..
            } => vec![*value_arg, *container_arg],
            Self::NonZero { arg, .. }
            | Self::PowerOfTwo { arg, .. }
            | Self::UnicodeScalar { arg, .. }
            | Self::Arg { arg, .. } => vec![*arg],
            Self::Args { args, .. } => args.clone(),
            Self::Predicate { predicate, .. } => predicate.arg_indices(),
            Self::NoArgs { .. } => Vec::new(),
            Self::OffsetInAlloc {
                offset_arg,
                ptr_arg,
                ..
            } => vec![*offset_arg, *ptr_arg],
        }
    }

    fn contract_spec(&self) -> Option<BindingContractSpec> {
        match self {
            Self::Predicate { predicate, .. } => Some(BindingContractSpec {
                raw_tag: predicate.raw().to_owned(),
                sp: predicate.kind().clone(),
                usage: self.usage(),
            }),
            Self::LtLen { .. } | Self::OffsetInAlloc { .. } => Some(BindingContractSpec {
                raw_tag: "InBounded".to_owned(),
                sp: PrimitiveSpKind::InBound,
                usage: self.usage(),
            }),
            Self::NonZero { .. } | Self::PowerOfTwo { .. } => Some(BindingContractSpec {
                raw_tag: "ValidNum".to_owned(),
                sp: PrimitiveSpKind::ValidNum,
                usage: self.usage(),
            }),
            Self::UnicodeScalar { .. } => Some(BindingContractSpec {
                raw_tag: "ValidString".to_owned(),
                sp: PrimitiveSpKind::ValidString,
                usage: self.usage(),
            }),
            Self::Arg {
                sp: Some(raw_tag), ..
            }
            | Self::Args {
                sp: Some(raw_tag), ..
            }
            | Self::NoArgs {
                sp: Some(raw_tag), ..
            } => Some(BindingContractSpec {
                raw_tag: raw_tag.clone(),
                sp: PrimitiveSpKind::from_tag(raw_tag),
                usage: self.usage(),
            }),
            Self::Arg { sp: None, .. }
            | Self::Args { sp: None, .. }
            | Self::NoArgs { sp: None, .. } => None,
        }
    }
}

fn default_contract_usage_for_sp(sp: &PrimitiveSpKind) -> ContractUsage {
    match sp {
        PrimitiveSpKind::TraitCopy => ContractUsage::Option,
        _ => ContractUsage::Precondition,
    }
}

#[derive(Default)]
struct PlaceResolver {
    aliases: HashMap<usize, SymbolicPlace>,
    flow_aliases: HashMap<usize, SymbolicPlace>,
}

struct LazyDataFlowGraphs<'tcx> {
    analyzer: RefCell<DataFlowAnalyzer<'tcx>>,
    cache: RefCell<HashMap<DefId, Option<DataFlowGraph>>>,
}

impl<'tcx> LazyDataFlowGraphs<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            analyzer: RefCell::new(DataFlowAnalyzer::new(tcx, false)),
            cache: RefCell::new(HashMap::new()),
        }
    }

    fn get(&self, fn_did: DefId) -> Option<DataFlowGraph> {
        if let Some(cached) = self.cache.borrow().get(&fn_did) {
            return cached.clone();
        }

        let graph = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.analyzer
                .borrow_mut()
                .get_or_build_fn_dataflow_lightweight(fn_did)
        }))
        .ok()
        .flatten();
        self.cache.borrow_mut().insert(fn_did, graph.clone());
        graph
    }
}

impl PlaceResolver {
    fn for_fn(
        tcx: TyCtxt<'_>,
        fn_did: DefId,
        dataflow_graphs: Option<&LazyDataFlowGraphs<'_>>,
    ) -> Self {
        let flow_aliases = dataflow_graphs
            .and_then(|graphs| graphs.get(fn_did))
            .map(|graph| dataflow_flow_aliases(tcx, fn_did, &graph))
            .unwrap_or_default();
        Self {
            aliases: HashMap::new(),
            flow_aliases,
        }
    }

    fn resolve_place(
        &self,
        tcx: TyCtxt<'_>,
        fn_did: DefId,
        place: &Place<'_>,
    ) -> Option<SymbolicPlace> {
        let raw = raw_symbolic_place(tcx, fn_did, place)?;
        if let PlaceRoot::Local(local) = raw.root {
            if let Some(alias) = self.aliases.get(&local) {
                return Some(alias.appended(&raw.fields));
            }
            if let Some(alias) = self.flow_aliases.get(&local) {
                return Some(alias.appended(&raw.fields));
            }
        }
        Some(raw)
    }

    fn resolve_operand(
        &self,
        tcx: TyCtxt<'_>,
        fn_did: DefId,
        operand: &Operand<'_>,
    ) -> Option<SymbolicPlace> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.resolve_place(tcx, fn_did, place),
            Operand::Constant(_) => None,
        }
    }

    fn record_alias(&mut self, lhs: &Place<'_>, rhs: SymbolicPlace) {
        if lhs.projection.is_empty() {
            self.aliases.insert(lhs.local.as_usize(), rhs);
        }
    }
}

fn dataflow_flow_aliases(
    tcx: TyCtxt<'_>,
    fn_did: DefId,
    graph: &DataFlowGraph,
) -> HashMap<usize, SymbolicPlace> {
    const MAX_ORIGIN_DEPTH: usize = 64;
    const MAX_SUFFIX_FIELDS: usize = 8;

    let body = tcx.optimized_mir(fn_did);
    let n_locals = body.local_decls.len();
    let mut aliases = HashMap::new();

    for local_idx in 0..n_locals {
        if !matches!(
            place_root_for_local(tcx, fn_did, local_idx),
            PlaceRoot::Local(_)
        ) {
            continue;
        }

        let local = Local::from_usize(local_idx);
        let mut visited = BTreeSet::new();
        if let Some(origin) = dataflow_origin_for_local(
            tcx,
            fn_did,
            graph,
            n_locals,
            local,
            Vec::new(),
            &mut visited,
            0,
            MAX_ORIGIN_DEPTH,
            MAX_SUFFIX_FIELDS,
        ) {
            if !matches!(origin.root, PlaceRoot::Local(_)) || !origin.fields.is_empty() {
                aliases.insert(local_idx, origin);
            }
        }
    }

    aliases
}

fn dataflow_origin_for_local(
    tcx: TyCtxt<'_>,
    fn_did: DefId,
    graph: &DataFlowGraph,
    n_locals: usize,
    local: Local,
    suffix_fields: Vec<usize>,
    visited: &mut BTreeSet<(usize, Vec<usize>)>,
    depth: usize,
    max_depth: usize,
    max_suffix_fields: usize,
) -> Option<SymbolicPlace> {
    if depth > max_depth || suffix_fields.len() > max_suffix_fields {
        return None;
    }
    if local.as_usize() >= graph.nodes.len() {
        return None;
    }
    if !visited.insert((local.as_usize(), suffix_fields.clone())) {
        return None;
    }

    let mut candidates = Vec::new();
    for edge_idx in graph.nodes[local].in_edges.iter().copied() {
        let edge = &graph.edges[edge_idx];
        let mut next_suffix = suffix_fields.clone();
        if let EdgeOp::Field(raw_field) = &edge.op {
            let Some(field_idx) = parse_dataflow_field_index(raw_field) else {
                continue;
            };
            next_suffix.insert(0, field_idx);
        }

        if let Some(origin) = dataflow_origin_for_local(
            tcx,
            fn_did,
            graph,
            n_locals,
            edge.src,
            next_suffix,
            visited,
            depth + 1,
            max_depth,
            max_suffix_fields,
        ) {
            candidates.push(origin);
        }
    }

    if local.as_usize() < n_locals {
        let root = place_root_for_local(tcx, fn_did, local.as_usize());
        if !matches!(root, PlaceRoot::Local(_)) || !suffix_fields.is_empty() {
            candidates.push(SymbolicPlace {
                root,
                fields: suffix_fields,
            });
        }
    }

    candidates.into_iter().max_by_key(symbolic_origin_score)
}

fn parse_dataflow_field_index(raw_field: &str) -> Option<usize> {
    let digits = raw_field
        .chars()
        .filter(|ch| ch.is_ascii_digit())
        .collect::<String>();
    digits.parse().ok()
}

fn symbolic_origin_score(place: &SymbolicPlace) -> (usize, usize) {
    let root_score = match place.root {
        PlaceRoot::Receiver => 4,
        PlaceRoot::Param(_) => 3,
        PlaceRoot::Return => 2,
        PlaceRoot::Local(_) => 1,
    };
    (root_score, place.fields.len())
}

#[derive(Clone)]
pub struct ContractGuide<'tcx> {
    tcx: TyCtxt<'tcx>,
    instances: Vec<ContractInstance>,
    effects: Vec<ContractEffect>,
    pairs: Vec<ConflictPair>,
    direct_hints: Vec<DirectSinkHint>,
    hazard_targets: Vec<HazardTarget>,
    hazard_temporal_plans: Vec<HazardTemporalPlan>,
    public_field_targets: Vec<PublicFieldTarget>,
    chain_scheduler: ChainScheduler,
    contract_db_loaded: bool,
    _marker: std::marker::PhantomData<&'tcx ()>,
}

impl<'tcx> ContractGuide<'tcx> {
    #[allow(dead_code)]
    pub fn analyze(tcx: TyCtxt<'tcx>) -> Self {
        let candidates = local_fn_candidates(tcx);
        Self::analyze_with_candidates(tcx, &candidates)
    }

    pub fn analyze_from_api_graph(tcx: TyCtxt<'tcx>, api_graph: &ApiDependencyGraph<'tcx>) -> Self {
        let candidates = api_graph.api_def_ids();
        rap_info!(
            "contract guide: use {} API dependency candidates",
            candidates.len()
        );
        Self::analyze_with_candidates(tcx, &candidates)
    }

    fn analyze_with_candidates(tcx: TyCtxt<'tcx>, candidate_fns: &[DefId]) -> Self {
        rap_info!("contract guide: initialize lazy dataflow cache");
        let dataflow_graphs = LazyDataFlowGraphs::new(tcx);
        let contract_db = match SafetyContractDb::load_default() {
            Ok(db) => {
                rap_info!("contract guide: collect lifted contracts");
                let instances = collect_lifted_contracts(tcx, &db, &dataflow_graphs, candidate_fns);
                rap_info!(
                    "contract guide: collected {} lifted contracts",
                    instances.len()
                );
                rap_info!("contract guide: collect mutating effects");
                let effects = collect_effects(tcx, &dataflow_graphs, candidate_fns);
                rap_info!("contract guide: collected {} effects", effects.len());
                rap_info!("contract guide: build conflicts");
                let (pairs, direct_hints, hazard_targets) =
                    build_conflicts(tcx, &instances, &effects);
                rap_info!(
                    "contract guide: built {} pairs, {} direct hints, and {} hazard targets",
                    pairs.len(),
                    direct_hints.len(),
                    hazard_targets.len()
                );
                rap_info!("contract guide: collect public field targets");
                let public_field_targets = collect_public_field_targets(tcx, &instances);
                rap_info!(
                    "contract guide: collected {} public field targets",
                    public_field_targets.len()
                );
                let hazard_temporal_plans = build_hazard_temporal_plans(tcx, &hazard_targets);
                return Self {
                    tcx,
                    instances,
                    effects,
                    pairs,
                    direct_hints,
                    hazard_targets,
                    hazard_temporal_plans,
                    public_field_targets,
                    chain_scheduler: ChainScheduler::default(),
                    contract_db_loaded: true,
                    _marker: std::marker::PhantomData,
                };
            }
            Err(_) => SafetyContractDb::default(),
        };

        rap_info!("contract guide: collect lifted contracts without std db");
        let instances =
            collect_lifted_contracts(tcx, &contract_db, &dataflow_graphs, candidate_fns);
        rap_info!(
            "contract guide: collected {} lifted contracts",
            instances.len()
        );
        rap_info!("contract guide: collect mutating effects");
        let effects = collect_effects(tcx, &dataflow_graphs, candidate_fns);
        rap_info!("contract guide: collected {} effects", effects.len());
        rap_info!("contract guide: build conflicts");
        let (pairs, direct_hints, hazard_targets) = build_conflicts(tcx, &instances, &effects);
        rap_info!(
            "contract guide: built {} pairs, {} direct hints, and {} hazard targets",
            pairs.len(),
            direct_hints.len(),
            hazard_targets.len()
        );
        rap_info!("contract guide: collect public field targets");
        let public_field_targets = collect_public_field_targets(tcx, &instances);
        rap_info!(
            "contract guide: collected {} public field targets",
            public_field_targets.len()
        );
        let hazard_temporal_plans = build_hazard_temporal_plans(tcx, &hazard_targets);
        Self {
            tcx,
            instances,
            effects,
            pairs,
            direct_hints,
            hazard_targets,
            hazard_temporal_plans,
            public_field_targets,
            chain_scheduler: ChainScheduler::default(),
            contract_db_loaded: false,
            _marker: std::marker::PhantomData,
        }
    }

    pub fn dump_to(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> io::Result<()> {
        let mut file = File::create(path)?;
        writeln!(file, "{}", self.summary(tcx))
    }

    pub fn contract_instance_records(&self, tcx: TyCtxt<'tcx>) -> Vec<ContractInstanceRecord> {
        self.instances
            .iter()
            .enumerate()
            .map(|(id, instance)| ContractInstanceRecord {
                schema_version: TESTGEN_ARTIFACT_SCHEMA_VERSION,
                id,
                stable_id: contract_stable_id(tcx, id, instance),
                contract_edge_id: contract_edge_id(tcx, id, instance),
                sink_fn: tcx.def_path_str(instance.sink_fn),
                sink_def_id: def_id_str(instance.sink_fn),
                sink_self_ty: instance.sink_self_ty.clone(),
                sink_signature: instance.sink_signature.clone(),
                sink_requires_monomorphization: instance.sink_requires_monomorphization,
                std_fn: instance.std_fn_name.clone(),
                std_fn_def_id: def_id_str(instance.std_fn),
                adt_def: instance.adt_def.map(|def_id| tcx.def_path_str(def_id)),
                sp: sp_name(&instance.sp),
                family: sp_family_name(&instance.sp),
                raw_tag: instance.raw_tag.clone(),
                symbolic_args: instance
                    .symbolic_args
                    .iter()
                    .map(|place| symbolic_place_display(tcx, instance.adt_def, place))
                    .collect(),
                usage: instance.usage.name().to_owned(),
                numeric_template: instance.numeric_kind.map(|kind| kind.name().to_owned()),
                binding_role: instance.binding_role.clone(),
            })
            .collect()
    }

    pub fn contract_instances_file(&self, tcx: TyCtxt<'tcx>) -> ContractInstancesFile {
        let instances = self.contract_instance_records(tcx);
        ContractInstancesFile {
            schema_version: TESTGEN_ARTIFACT_SCHEMA_VERSION,
            db_loaded: self.contract_db_loaded,
            total: instances.len(),
            instances,
        }
    }

    pub fn dump_instances_json(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> io::Result<()> {
        self.contract_instances_file(tcx).write_json(path)
    }

    pub fn cgag_file(&self, tcx: TyCtxt<'tcx>) -> CcagFile {
        let mut nodes = BTreeMap::new();
        let mut edges = Vec::new();

        for (contract_id, instance) in self.instances.iter().enumerate() {
            let sink_id = action_api_node_id(instance.sink_fn);
            insert_ccag_node(
                &mut nodes,
                sink_id.clone(),
                "action",
                tcx.def_path_str(instance.sink_fn),
                attrs(&[
                    ("action_kind", "public_api".to_owned()),
                    ("def_id", def_id_str(instance.sink_fn)),
                    ("self_ty", instance.sink_self_ty.clone().unwrap_or_default()),
                    ("signature", instance.sink_signature.clone()),
                    (
                        "requires_monomorphization",
                        instance.sink_requires_monomorphization.to_string(),
                    ),
                ]),
            );

            for (arg_idx, place) in instance.symbolic_args.iter().enumerate() {
                let place_id =
                    insert_state_field_path(tcx, &mut nodes, &mut edges, place, instance.adt_def);
                edges.push(ccag_edge(
                    sink_id.clone(),
                    place_id.clone(),
                    "uses",
                    format!("uses arg{arg_idx}"),
                    attrs(&[
                        (
                            "contract_edge_id",
                            contract_edge_id(tcx, contract_id, instance),
                        ),
                        ("role", format!("arg{arg_idx}")),
                    ]),
                ));
            }

            let primary_place = instance
                .sensitive_place()
                .cloned()
                .unwrap_or_else(|| implicit_contract_place(contract_id));
            let primary_place_id = insert_state_field_path(
                tcx,
                &mut nodes,
                &mut edges,
                &primary_place,
                instance.adt_def,
            );
            edges.push(ccag_edge(
                primary_place_id,
                sink_id,
                "contract",
                sp_name(&instance.sp),
                attrs(&[
                    ("contract_id", contract_id.to_string()),
                    (
                        "contract_edge_id",
                        contract_edge_id(tcx, contract_id, instance),
                    ),
                    ("sp", sp_name(&instance.sp)),
                    ("family", sp_family_name(&instance.sp)),
                    ("usage", instance.usage.name().to_owned()),
                    ("raw_tag", instance.raw_tag.clone()),
                    ("std_fn", instance.std_fn_name.clone()),
                    ("std_fn_def_id", def_id_str(instance.std_fn)),
                    (
                        "binding_role",
                        instance.binding_role.clone().unwrap_or_default(),
                    ),
                    ("roles", instance.args_display(tcx)),
                    (
                        "generic_preference",
                        format!("{:?}", generic_preference_for_instance(instance)),
                    ),
                ]),
            ));
        }

        for effect in &self.effects {
            let action_id = action_api_node_id(effect.fn_did);
            insert_ccag_node(
                &mut nodes,
                action_id.clone(),
                "action",
                tcx.def_path_str(effect.fn_did),
                attrs(&[
                    ("action_kind", "public_api".to_owned()),
                    ("def_id", def_id_str(effect.fn_did)),
                    ("effect", effect.kind.name().to_owned()),
                    ("confidence", effect.confidence.name().to_owned()),
                ]),
            );

            let output = effect.kind.primary_place();
            let output_id =
                insert_state_field_path(tcx, &mut nodes, &mut edges, output, effect.adt_def);
            edges.push(ccag_edge(
                action_id.clone(),
                output_id,
                "mutates",
                effect.kind.name(),
                attrs(&[
                    ("source", "method".to_owned()),
                    ("confidence", effect.confidence.name().to_owned()),
                ]),
            ));

            for input in effect
                .kind
                .input_places()
                .iter()
                .filter(|place| place.is_receiver_field())
            {
                let input_id =
                    insert_state_field_path(tcx, &mut nodes, &mut edges, input, effect.adt_def);
                edges.push(ccag_edge(
                    action_id.clone(),
                    input_id,
                    "uses",
                    "uses field",
                    attrs(&[
                        ("source", "method_effect_input".to_owned()),
                        ("confidence", effect.confidence.name().to_owned()),
                    ]),
                ));
            }
        }

        for pair in &self.pairs {
            let producer_id = action_api_node_id(pair.producer_fn);
            insert_ccag_node(
                &mut nodes,
                producer_id.clone(),
                "action",
                tcx.def_path_str(pair.producer_fn),
                attrs(&[
                    ("action_kind", "public_api".to_owned()),
                    ("def_id", def_id_str(pair.producer_fn)),
                    ("effect", pair.effect_kind.to_owned()),
                    ("confidence", pair.effect_confidence.to_owned()),
                ]),
            );
            let pair_adt_def = self
                .instances
                .get(pair.contract_id)
                .and_then(|instance| instance.adt_def)
                .or_else(|| get_adt_def_id_by_adt_method(tcx, pair.producer_fn));
            let place_id =
                insert_state_field_path(tcx, &mut nodes, &mut edges, &pair.place, pair_adt_def);
            edges.push(ccag_edge(
                producer_id,
                place_id,
                "mutates",
                pair.effect_kind,
                attrs(&[
                    ("source", "method".to_owned()),
                    ("contract_id", pair.contract_id.to_string()),
                    (
                        "contract_edge_id",
                        contract_edge_id(tcx, pair.contract_id, &self.instances[pair.contract_id]),
                    ),
                    ("sp", sp_name(&pair.sp)),
                    ("confidence", pair.effect_confidence.to_owned()),
                    ("reason", pair.reason.clone()),
                ]),
            ));
            if let Some(hint) = &pair.hint {
                let recipe_id =
                    recipe_action_node_id(pair.contract_id, &format!("{:?}", hint.kind));
                insert_ccag_node(
                    &mut nodes,
                    recipe_id.clone(),
                    "action",
                    format!("{:?}", hint.kind),
                    attrs(&[
                        ("action_kind", "resource_recipe".to_owned()),
                        ("reason", hint.reason.clone()),
                    ]),
                );
                edges.push(ccag_edge(
                    recipe_id,
                    place_node_id(&pair.place),
                    "mutates",
                    "recipe",
                    attrs(&[
                        ("source", "recipe".to_owned()),
                        ("contract_id", pair.contract_id.to_string()),
                        (
                            "contract_edge_id",
                            contract_edge_id(
                                tcx,
                                pair.contract_id,
                                &self.instances[pair.contract_id],
                            ),
                        ),
                        ("hint", format!("{:?}", hint.kind)),
                        ("reason", hint.reason.clone()),
                    ]),
                ));
            }
        }

        for target in &self.hazard_targets {
            let Some(instance) = self.instances.get(target.contract_id) else {
                continue;
            };
            let post_id = action_api_node_id(target.post_fn);
            insert_ccag_node(
                &mut nodes,
                post_id.clone(),
                "action",
                tcx.def_path_str(target.post_fn),
                attrs(&[
                    ("action_kind", "public_api".to_owned()),
                    ("def_id", def_id_str(target.post_fn)),
                    ("effect", target.effect_kind.to_owned()),
                    ("confidence", target.effect_confidence.to_owned()),
                    ("phase", "after_hazard_sink".to_owned()),
                ]),
            );
            let target_adt_def = instance
                .adt_def
                .or_else(|| get_adt_def_id_by_adt_method(tcx, target.post_fn));
            let place_id =
                insert_state_field_path(tcx, &mut nodes, &mut edges, &target.place, target_adt_def);
            edges.push(ccag_edge(
                post_id,
                place_id,
                "mutates",
                target.effect_kind,
                attrs(&[
                    ("source", "hazard_post_call".to_owned()),
                    ("phase", "after_hazard_sink".to_owned()),
                    ("usage", instance.usage.name().to_owned()),
                    ("contract_id", target.contract_id.to_string()),
                    (
                        "contract_edge_id",
                        contract_edge_id(tcx, target.contract_id, instance),
                    ),
                    ("sp", sp_name(&target.sp)),
                    ("confidence", target.effect_confidence.to_owned()),
                    ("reason", target.reason.clone()),
                ]),
            ));
        }

        for target in &self.public_field_targets {
            let mutator_id = public_field_action_node_id(target);
            insert_ccag_node(
                &mut nodes,
                mutator_id.clone(),
                "action",
                format!("{}.{}", tcx.def_path_str(target.adt_def), target.field_name),
                attrs(&[
                    ("action_kind", "public_field_assignment".to_owned()),
                    ("adt_def", tcx.def_path_str(target.adt_def)),
                    ("field", target.field_name.clone()),
                    ("field_path", format!("{:?}", target.field_path)),
                    ("effect", "PublicFieldWrite".to_owned()),
                    ("contract_id", target.contract_id.to_string()),
                    ("reason", target.reason.clone()),
                ]),
            );
            let place_id = insert_state_field_path(
                tcx,
                &mut nodes,
                &mut edges,
                &target.place,
                Some(target.adt_def),
            );
            edges.push(ccag_edge(
                mutator_id.clone(),
                place_id.clone(),
                "mutates",
                "public field write",
                attrs(&[
                    ("source", "public_field".to_owned()),
                    ("contract_id", target.contract_id.to_string()),
                    (
                        "contract_edge_id",
                        contract_edge_id(
                            tcx,
                            target.contract_id,
                            &self.instances[target.contract_id],
                        ),
                    ),
                    ("sp", sp_name(&target.sp)),
                    ("field", target.field_name.clone()),
                    ("field_path", format!("{:?}", target.field_path)),
                    ("reason", target.reason.clone()),
                ]),
            ));
            if let Some(hint) = &target.hint {
                let recipe_id =
                    recipe_action_node_id(target.contract_id, &format!("{:?}", hint.kind));
                insert_ccag_node(
                    &mut nodes,
                    recipe_id.clone(),
                    "action",
                    format!("{:?}", hint.kind),
                    attrs(&[
                        ("action_kind", "resource_recipe".to_owned()),
                        ("reason", hint.reason.clone()),
                    ]),
                );
                edges.push(ccag_edge(
                    recipe_id,
                    place_id,
                    "mutates",
                    "recipe",
                    attrs(&[
                        ("source", "recipe".to_owned()),
                        ("contract_id", target.contract_id.to_string()),
                        (
                            "contract_edge_id",
                            contract_edge_id(
                                tcx,
                                target.contract_id,
                                &self.instances[target.contract_id],
                            ),
                        ),
                        ("hint", format!("{:?}", hint.kind)),
                        ("reason", hint.reason.clone()),
                    ]),
                ));
            }
        }

        for direct in &self.direct_hints {
            let Some(instance) = self.instances.get(direct.contract_id) else {
                continue;
            };
            let recipe_id =
                recipe_action_node_id(direct.contract_id, &format!("{:?}", direct.hint.kind));
            insert_ccag_node(
                &mut nodes,
                recipe_id.clone(),
                "action",
                format!("{:?}", direct.hint.kind),
                attrs(&[
                    ("action_kind", "resource_recipe".to_owned()),
                    ("reason", direct.reason.clone()),
                ]),
            );
            let place = instance
                .sensitive_place()
                .cloned()
                .unwrap_or_else(|| implicit_contract_place(direct.contract_id));
            let place_id =
                insert_state_field_path(tcx, &mut nodes, &mut edges, &place, instance.adt_def);
            edges.push(ccag_edge(
                recipe_id,
                place_id,
                "mutates",
                format!("arg{}", direct.param_idx),
                attrs(&[
                    ("source", "direct_input".to_owned()),
                    ("param", direct.param_idx.to_string()),
                    ("contract_id", direct.contract_id.to_string()),
                    (
                        "contract_edge_id",
                        contract_edge_id(tcx, direct.contract_id, instance),
                    ),
                    ("hint", format!("{:?}", direct.hint.kind)),
                    ("reason", direct.reason.clone()),
                ]),
            ));
        }

        CcagFile::from_parts(nodes.into_values().collect(), edges)
    }

    pub fn ccag_file(&self, tcx: TyCtxt<'tcx>) -> CcagFile {
        self.cgag_file(tcx)
    }

    pub fn dump_cgag_json(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> io::Result<()> {
        self.cgag_file(tcx).write_json(path)
    }

    pub fn dump_cgag_dot(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> io::Result<()> {
        self.cgag_file(tcx).write_dot(path)
    }

    pub fn dump_ccag_json(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> io::Result<()> {
        self.ccag_file(tcx).write_json(path)
    }

    pub fn dump_ccag_dot(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> io::Result<()> {
        self.ccag_file(tcx).write_dot(path)
    }

    pub fn violation_edge_contract_ids(&self) -> BTreeSet<usize> {
        self.pairs
            .iter()
            .map(|pair| pair.contract_id)
            .chain(self.direct_hints.iter().map(|hint| hint.contract_id))
            .chain(self.hazard_targets.iter().map(|target| target.contract_id))
            .chain(
                self.public_field_targets
                    .iter()
                    .map(|target| target.contract_id),
            )
            .collect()
    }

    pub fn case_metadata(
        &self,
        case_name: impl Into<String>,
        case_path: impl Into<std::path::PathBuf>,
        cx: &crate::analysis::testgen::context::Context<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> CaseMetadata {
        let mut metadata = CaseMetadata::from_context(case_name, case_path, cx, tcx);
        metadata.targets = self.case_targets(cx, tcx);
        metadata
    }

    fn case_targets(
        &self,
        cx: &crate::analysis::testgen::context::Context<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Vec<CaseTargetRecord> {
        let mut call_positions: HashMap<DefId, Vec<usize>> = HashMap::new();
        let ref_source = ref_source_map(cx.stmts());
        let mut field_assign_positions = Vec::new();
        for (idx, stmt) in cx.stmts().iter().enumerate() {
            match stmt.kind() {
                StmtKind::Call(call) => {
                    call_positions.entry(call.fn_did()).or_default().push(idx);
                }
                StmtKind::FieldAssign {
                    base, field_name, ..
                } => {
                    field_assign_positions.push((idx, *base, field_name.clone()));
                }
                _ => {}
            }
        }

        let mut targets = Vec::new();
        for pair in &self.pairs {
            let Some(producer_positions) = call_positions.get(&pair.producer_fn) else {
                continue;
            };
            let Some(instance) = self.instances.get(pair.contract_id) else {
                continue;
            };
            let sink_positions = call_positions
                .get(&pair.sink_fn)
                .into_iter()
                .flatten()
                .copied()
                .filter(|idx| {
                    cx.stmts()
                        .get(*idx)
                        .and_then(|stmt| match stmt.kind() {
                            StmtKind::Call(call) => {
                                Some(call_matches_contract_instance(instance, call))
                            }
                            _ => None,
                        })
                        .unwrap_or(false)
                })
                .collect_vec();
            if sink_positions.is_empty() {
                continue;
            }
            if !producer_positions
                .iter()
                .any(|producer| sink_positions.iter().any(|sink| producer <= sink))
            {
                continue;
            }
            targets.push(CaseTargetRecord {
                contract_id: pair.contract_id,
                contract_stable_id: contract_stable_id(tcx, pair.contract_id, instance),
                contract_edge_id: contract_edge_id(tcx, pair.contract_id, instance),
                target_kind: "producer_sink".to_owned(),
                producer_fn: Some(tcx.def_path_str(pair.producer_fn)),
                sink_fn: tcx.def_path_str(pair.sink_fn),
                std_fn: instance.std_fn_name.clone(),
                sp: sp_name(&instance.sp),
                family: sp_family_name(&instance.sp),
                usage: instance.usage.name().to_owned(),
                effect_kind: Some(pair.effect_kind.to_owned()),
                effect_confidence: Some(pair.effect_confidence.to_owned()),
                hint_param: pair.hint_param,
                hint_kind: pair.hint.as_ref().map(|hint| format!("{:?}", hint.kind)),
                reason: pair.reason.clone(),
            });
        }

        for direct in &self.direct_hints {
            let Some(instance) = self.instances.get(direct.contract_id) else {
                continue;
            };
            let has_sink = call_positions
                .get(&direct.sink_fn)
                .into_iter()
                .flatten()
                .any(|idx| {
                    cx.stmts()
                        .get(*idx)
                        .and_then(|stmt| match stmt.kind() {
                            StmtKind::Call(call) => {
                                Some(call_matches_contract_instance(instance, call))
                            }
                            _ => None,
                        })
                        .unwrap_or(false)
                });
            if !has_sink {
                continue;
            }
            targets.push(CaseTargetRecord {
                contract_id: direct.contract_id,
                contract_stable_id: contract_stable_id(tcx, direct.contract_id, instance),
                contract_edge_id: contract_edge_id(tcx, direct.contract_id, instance),
                target_kind: "direct_sink".to_owned(),
                producer_fn: None,
                sink_fn: tcx.def_path_str(direct.sink_fn),
                std_fn: instance.std_fn_name.clone(),
                sp: sp_name(&instance.sp),
                family: sp_family_name(&instance.sp),
                usage: instance.usage.name().to_owned(),
                effect_kind: None,
                effect_confidence: None,
                hint_param: Some(direct.param_idx),
                hint_kind: Some(format!("{:?}", direct.hint.kind)),
                reason: direct.reason.clone(),
            });
        }

        for hazard in &self.hazard_targets {
            let Some(instance) = self.instances.get(hazard.contract_id) else {
                continue;
            };
            let Some(post_positions) = call_positions.get(&hazard.post_fn) else {
                continue;
            };
            let mut matched = false;
            for &post_idx in post_positions {
                let Some(post_receiver) = cx.stmts().get(post_idx).and_then(|stmt| {
                    let StmtKind::Call(call) = stmt.kind() else {
                        return None;
                    };
                    call.args().first().copied()
                }) else {
                    continue;
                };
                let post_receiver = normalize_ref_var(post_receiver, &ref_source);
                for (sink_idx, stmt) in cx.stmts().iter().enumerate() {
                    if sink_idx > post_idx {
                        break;
                    }
                    let StmtKind::Call(call) = stmt.kind() else {
                        continue;
                    };
                    if !call_matches_contract_instance(instance, call) {
                        continue;
                    }
                    let Some(sink_receiver) = call.args().first().copied() else {
                        continue;
                    };
                    if normalize_ref_var(sink_receiver, &ref_source) == post_receiver {
                        matched = true;
                        break;
                    }
                }
                if matched {
                    break;
                }
            }
            if !matched {
                continue;
            }
            targets.push(CaseTargetRecord {
                contract_id: hazard.contract_id,
                contract_stable_id: contract_stable_id(tcx, hazard.contract_id, instance),
                contract_edge_id: contract_edge_id(tcx, hazard.contract_id, instance),
                target_kind: "hazard_post".to_owned(),
                producer_fn: Some(tcx.def_path_str(hazard.post_fn)),
                sink_fn: tcx.def_path_str(hazard.sink_fn),
                std_fn: instance.std_fn_name.clone(),
                sp: sp_name(&instance.sp),
                family: sp_family_name(&instance.sp),
                usage: instance.usage.name().to_owned(),
                effect_kind: Some(hazard.effect_kind.to_owned()),
                effect_confidence: Some(hazard.effect_confidence.to_owned()),
                hint_param: None,
                hint_kind: None,
                reason: hazard.reason.clone(),
            });
        }

        for public_field in &self.public_field_targets {
            let Some(instance) = self.instances.get(public_field.contract_id) else {
                continue;
            };
            let mut matched = false;
            for (assign_idx, assigned_base, field_name) in &field_assign_positions {
                if field_name != &public_field.field_name {
                    continue;
                }
                for (sink_idx, stmt) in cx.stmts().iter().enumerate() {
                    if sink_idx < *assign_idx {
                        continue;
                    }
                    let StmtKind::Call(call) = stmt.kind() else {
                        continue;
                    };
                    if !call_matches_contract_instance(instance, call) {
                        continue;
                    }
                    let Some(receiver) = call.args().first().copied() else {
                        continue;
                    };
                    if normalize_ref_var(receiver, &ref_source) == *assigned_base {
                        matched = true;
                        break;
                    }
                }
                if matched {
                    break;
                }
            }
            if !matched {
                continue;
            }
            targets.push(CaseTargetRecord {
                contract_id: public_field.contract_id,
                contract_stable_id: contract_stable_id(tcx, public_field.contract_id, instance),
                contract_edge_id: contract_edge_id(tcx, public_field.contract_id, instance),
                target_kind: "public_field".to_owned(),
                producer_fn: None,
                sink_fn: tcx.def_path_str(public_field.sink_fn),
                std_fn: instance.std_fn_name.clone(),
                sp: sp_name(&instance.sp),
                family: sp_family_name(&instance.sp),
                usage: instance.usage.name().to_owned(),
                effect_kind: Some("PublicFieldWrite".to_owned()),
                effect_confidence: Some("exact".to_owned()),
                hint_param: None,
                hint_kind: public_field
                    .hint
                    .as_ref()
                    .map(|hint| format!("{:?}", hint.kind)),
                reason: public_field.reason.clone(),
            });
        }

        targets.sort_by_key(|target| {
            (
                target.contract_id,
                target.target_kind.clone(),
                target.producer_fn.clone(),
                target.sink_fn.clone(),
            )
        });
        targets.dedup_by(|lhs, rhs| {
            lhs.contract_id == rhs.contract_id
                && lhs.target_kind == rhs.target_kind
                && lhs.producer_fn == rhs.producer_fn
                && lhs.sink_fn == rhs.sink_fn
        });
        targets
    }

    fn hints_for_pairs(&self, call: &ApiCall<'tcx>) -> Vec<Option<InputHint>> {
        let mut hints = Vec::new();
        for pair in self
            .pairs
            .iter()
            .filter(|pair| pair.producer_fn == call.fn_did())
        {
            let Some(param_idx) = pair.hint_param else {
                continue;
            };
            if hints.len() <= param_idx {
                hints.resize(param_idx + 1, None);
            }
            if hints[param_idx].is_none() {
                hints[param_idx] = self
                    .instances
                    .get(pair.contract_id)
                    .and_then(|instance| {
                        self.expression_hint_for_call(
                            instance,
                            call,
                            format!("{} via {}", pair.reason, pair.effect_kind),
                        )
                        .map(|(_, hint)| hint)
                    })
                    .or_else(|| pair.hint.clone());
            }
        }
        hints
    }

    fn hints_for_direct_sink(&self, call: &ApiCall<'tcx>) -> Vec<Option<InputHint>> {
        let mut hints = Vec::new();
        for direct in self
            .direct_hints
            .iter()
            .filter(|direct| direct.sink_fn == call.fn_did())
        {
            let (param_idx, hint) = self
                .instances
                .get(direct.contract_id)
                .and_then(|instance| {
                    self.expression_hint_for_call(instance, call, direct.reason.clone())
                })
                .unwrap_or((direct.param_idx, direct.hint.clone()));
            if hints.len() <= param_idx {
                hints.resize(param_idx + 1, None);
            }
            if hints[param_idx].is_none() {
                hints[param_idx] = Some(hint);
            }
        }
        hints
    }

    fn expression_hint_for_call(
        &self,
        instance: &ContractInstance,
        call: &ApiCall<'tcx>,
        reason: impl Into<String>,
    ) -> Option<(usize, InputHint)> {
        if instance.sp != PrimitiveSpKind::ValidNum {
            return None;
        }
        let env = TypeSizeEnv::from_generic_args(self.tcx, call.generic_args());
        let (param_idx, mut hint) = direct_numeric_hint_for_predicate(&instance.raw_tag, &env)?;
        hint.reason = reason.into();
        Some((param_idx, hint))
    }

    fn has_prior_producer_for_receiver(
        &self,
        builder: &ContextBuilder<'tcx, '_>,
        pair: &ConflictPair,
        receiver: Var,
    ) -> bool {
        let mut ref_source = HashMap::new();
        for stmt in builder.cx().stmts() {
            if let StmtKind::Ref(source, _) | StmtKind::SliceRef(source, _) = stmt.kind() {
                ref_source.insert(stmt.place(), *source);
            }
        }

        let normalize = |mut var: Var| {
            while let Some(source) = ref_source.get(&var).copied() {
                var = source;
            }
            var
        };

        let receiver = normalize(receiver);
        builder.cx().stmts().iter().any(|stmt| {
            let StmtKind::Call(call) = stmt.kind() else {
                return false;
            };
            if call.fn_did() != pair.producer_fn {
                return false;
            }
            if pair.effect_kind == "ConstructAdt" {
                return stmt.place() == receiver;
            }
            let Some(producer_receiver) = call.args().first().copied() else {
                return false;
            };
            normalize(producer_receiver) == receiver
        })
    }

    fn has_prior_public_field_assignment(
        &self,
        builder: &ContextBuilder<'tcx, '_>,
        target: &PublicFieldTarget,
        receiver: Var,
    ) -> bool {
        builder.cx().stmts().iter().any(|stmt| {
            let StmtKind::FieldAssign {
                base, field_name, ..
            } = stmt.kind()
            else {
                return false;
            };
            *base == receiver && field_name == &target.field_name
        })
    }

    fn prior_hazard_witness_for_receiver(
        &self,
        builder: &ContextBuilder<'tcx, '_>,
        target: &HazardTarget,
        receiver: Var,
    ) -> Option<Var> {
        let Some(instance) = self.instances.get(target.contract_id) else {
            return None;
        };
        let ref_source = ref_source_map(builder.cx().stmts());
        let receiver = normalize_ref_var(receiver, &ref_source);

        for stmt in builder.cx().stmts().iter().rev() {
            let StmtKind::Call(call) = stmt.kind() else {
                continue;
            };
            if !call_matches_contract_instance(instance, call) {
                continue;
            }
            let Some(sink_receiver) = call.args().first().copied() else {
                continue;
            };
            if normalize_ref_var(sink_receiver, &ref_source) != receiver {
                continue;
            }
            let witness = stmt.place();
            if builder.var_state(witness).is_live() {
                return Some(witness);
            }
        }

        None
    }

    fn has_prior_hazard_witness_for_receiver(
        &self,
        builder: &ContextBuilder<'tcx, '_>,
        target: &HazardTarget,
        receiver: Var,
    ) -> bool {
        self.prior_hazard_witness_for_receiver(builder, target, receiver)
            .is_some()
    }

    fn try_insert_hazard_post_call(
        &self,
        call: &ApiCall<'tcx>,
        witness: Var,
        builder: &mut ContextBuilder<'tcx, '_>,
    ) {
        let Some(receiver) = call.args().first().copied() else {
            return;
        };
        let receiver_ty = builder.cx().type_of(receiver);
        for target in self
            .hazard_targets
            .iter()
            .filter(|target| target.sink_fn == call.fn_did())
        {
            if target.post_fn == target.sink_fn
                || self
                    .tcx
                    .generics_of(target.post_fn)
                    .requires_monomorphization(self.tcx)
            {
                continue;
            }
            let generic_args = self.tcx.mk_args(&[]);
            let fn_sig = utils::fn_sig_with_generic_args(target.post_fn, generic_args, self.tcx);
            let inputs = fn_sig.inputs();
            let Some(post_receiver_ty) = inputs.first() else {
                continue;
            };
            if !utils::is_ty_eq(*post_receiver_ty, receiver_ty, self.tcx) {
                continue;
            }
            let mut args = vec![receiver];
            args.extend((1..inputs.len()).map(|_| DUMMY_INPUT_VAR));
            let post_call = ApiCall {
                fn_did: target.post_fn,
                args,
                generic_args,
            };
            builder.add_call_stmt_with_hints(post_call, Vec::new());
            builder.add_sink_marker_stmt(target.contract_id, self.tcx.def_path_str(target.sink_fn));
            builder.try_add_observer_stmt_for(witness);
            break;
        }
    }

    fn has_called_contract_instance(
        &self,
        builder: &ContextBuilder<'tcx, '_>,
        instance: &ContractInstance,
    ) -> bool {
        builder.cx().stmts().iter().any(|stmt| {
            let StmtKind::Call(call) = stmt.kind() else {
                return false;
            };
            call_matches_contract_instance(instance, call)
        })
    }

    fn contract_target_for(
        &self,
        contract_id: usize,
        sink_fn: DefId,
        priority: f32,
        strategy: ChainStrategy,
    ) -> ContractTarget {
        ContractTarget {
            contract_id,
            sink_fn,
            priority: priority * self.chain_scheduler.priority_multiplier(strategy),
            generic_preference: self
                .instances
                .get(contract_id)
                .map(generic_preference_for_instance)
                .unwrap_or(ContractGenericPreference::Any),
            strategy,
        }
    }

    fn try_insert_public_field_mutation(
        &self,
        call: &ApiCall<'tcx>,
        builder: &mut ContextBuilder<'tcx, '_>,
    ) {
        let Some(receiver) = call.args().first().copied() else {
            return;
        };
        if receiver == DUMMY_INPUT_VAR {
            return;
        }

        let ref_source = ref_source_map(builder.cx().stmts());
        let receiver = normalize_ref_var(receiver, &ref_source);
        if !builder.var_state(receiver).is_live() {
            return;
        }

        let mut mutated_fields = BTreeSet::new();
        for target in self
            .public_field_targets
            .iter()
            .filter(|target| target.sink_fn == call.fn_did())
        {
            if mutated_fields.contains(&target.field_name) {
                continue;
            }
            if self.has_prior_public_field_assignment(builder, target, receiver) {
                continue;
            }
            let Some(field_ty) = field_ty_for_base(self.tcx(), builder, receiver, target) else {
                continue;
            };
            if builder
                .add_field_assign_stmt(
                    receiver,
                    target.field_name.clone(),
                    field_ty,
                    target.hint.clone(),
                )
                .is_some()
            {
                mutated_fields.insert(target.field_name.clone());
            }
        }
    }

    fn score_alignment_generic_action(&self, call: &ApiCall<'tcx>) -> f32 {
        let generic_score = high_alignment_generic_score(call.generic_args());
        if generic_score <= 0.0 {
            return 0.0;
        }

        let fn_did = call.fn_did();
        let mut score = 0.0;
        for instance in &self.instances {
            if !matches!(
                instance.sp,
                PrimitiveSpKind::Align | PrimitiveSpKind::DoubleAlign
            ) {
                continue;
            }

            if instance.sink_fn == fn_did {
                score += 240.0 * generic_score;
                continue;
            }

            let Some(sink_adt) = instance.adt_def else {
                continue;
            };
            let fn_sig = utils::fn_sig_with_generic_args(fn_did, call.generic_args(), self.tcx);
            if output_constructs_adt(fn_sig.output(), sink_adt) {
                score += 160.0 * generic_score;
            }
        }
        score
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

#[allow(dead_code)]
fn local_fn_candidates(tcx: TyCtxt<'_>) -> Vec<DefId> {
    tcx.hir_body_owners()
        .filter(|local_def_id| matches!(tcx.hir_body_owner_kind(*local_def_id), BodyOwnerKind::Fn))
        .map(|local_def_id| local_def_id.to_def_id())
        .filter(|fn_did| is_local_mir_fn(tcx, *fn_did))
        .collect()
}

fn is_local_mir_fn(tcx: TyCtxt<'_>, fn_did: DefId) -> bool {
    fn_did.is_local() && tcx.is_mir_available(fn_did)
}

impl<'tcx> FuzzGuide<'tcx> for ContractGuide<'tcx> {
    fn name(&self) -> &'static str {
        "contract"
    }

    fn score_action(
        &self,
        action: GuidedAction<'_, 'tcx>,
        builder: &ContextBuilder<'tcx, '_>,
    ) -> f32 {
        let fn_did = action.call.fn_did();
        let mut score = 0.0;

        for pair in &self.pairs {
            if pair.producer_fn == fn_did {
                score += match pair.hint_param {
                    Some(param_idx)
                        if action.call.args().get(param_idx) == Some(&DUMMY_INPUT_VAR) =>
                    {
                        100.0
                    }
                    Some(_) => 20.0,
                    None if pair.effect_kind == "ConstructAdt" => 140.0,
                    None => 80.0,
                };
            }
            if pair.sink_fn == fn_did {
                let Some(instance) = self.instances.get(pair.contract_id) else {
                    continue;
                };
                if !call_matches_contract_instance(instance, action.call) {
                    continue;
                }
                let receiver = action.call.args().first().copied();
                let ready = receiver
                    .map(|var| self.has_prior_producer_for_receiver(builder, pair, var))
                    .unwrap_or(false);
                score += if ready { 260.0 } else { 20.0 };
            }
        }

        for direct in &self.direct_hints {
            if direct.sink_fn == fn_did {
                let Some(instance) = self.instances.get(direct.contract_id) else {
                    continue;
                };
                if !call_matches_contract_instance(instance, action.call) {
                    continue;
                }
                score += if action.call.args().get(direct.param_idx) == Some(&DUMMY_INPUT_VAR) {
                    180.0
                } else {
                    20.0
                };
            }
        }

        for target in &self.hazard_targets {
            let Some(instance) = self.instances.get(target.contract_id) else {
                continue;
            };
            if target.sink_fn == fn_did {
                if !call_matches_contract_instance(instance, action.call) {
                    continue;
                }
                score += 180.0;
            }
            if target.post_fn == fn_did {
                let receiver = action.call.args().first().copied();
                let ready = receiver
                    .map(|var| self.has_prior_hazard_witness_for_receiver(builder, target, var))
                    .unwrap_or(false);
                score += if ready { 300.0 } else { 20.0 };
            }
        }

        for target in &self.public_field_targets {
            if target.sink_fn == fn_did {
                let Some(instance) = self.instances.get(target.contract_id) else {
                    continue;
                };
                if !call_matches_contract_instance(instance, action.call) {
                    continue;
                }
                let receiver = action.call.args().first().copied();
                let ready = receiver
                    .map(|var| {
                        let ref_source = ref_source_map(builder.cx().stmts());
                        let receiver = normalize_ref_var(var, &ref_source);
                        self.has_prior_public_field_assignment(builder, target, receiver)
                    })
                    .unwrap_or(false);
                score += if ready { 260.0 } else { 120.0 };
            }
        }

        score += self.score_alignment_generic_action(action.call);

        score
    }

    fn input_hints_for_call(
        &self,
        call: &ApiCall<'tcx>,
        _builder: &ContextBuilder<'tcx, '_>,
    ) -> Vec<Option<InputHint>> {
        merge_hints(self.hints_for_pairs(call), self.hints_for_direct_sink(call))
    }

    fn before_call(&self, call: &ApiCall<'tcx>, builder: &mut ContextBuilder<'tcx, '_>) {
        self.try_insert_public_field_mutation(call, builder);
        for (contract_id, instance) in self
            .instances
            .iter()
            .enumerate()
            .filter(|(_, instance)| call_matches_contract_instance(instance, call))
        {
            builder.add_sink_marker_stmt(contract_id, self.tcx.def_path_str(instance.sink_fn));
        }
    }

    fn after_call(&self, call: &ApiCall<'tcx>, place: Var, builder: &mut ContextBuilder<'tcx, '_>) {
        self.try_insert_hazard_post_call(call, place, builder);

        for target in self
            .hazard_targets
            .iter()
            .filter(|target| target.post_fn == call.fn_did())
        {
            let Some(receiver) = call.args().first().copied() else {
                continue;
            };
            let Some(witness) = self.prior_hazard_witness_for_receiver(builder, target, receiver)
            else {
                continue;
            };
            builder.add_sink_marker_stmt(target.contract_id, self.tcx.def_path_str(target.sink_fn));
            builder.try_add_observer_stmt_for(witness);
        }
    }

    fn contract_targets(&self, builder: &ContextBuilder<'tcx, '_>) -> Vec<ContractTarget> {
        let mut targets = Vec::new();
        for (contract_id, instance) in self.instances.iter().enumerate() {
            if matches!(instance.usage, ContractUsage::Option) {
                continue;
            }
            let already_called = builder.cx().stmts().iter().any(|stmt| {
                let StmtKind::Call(call) = stmt.kind() else {
                    return false;
                };
                call_matches_contract_instance(instance, call)
            });
            if already_called && !matches!(instance.usage, ContractUsage::Hazard) {
                continue;
            }
            targets.push(self.contract_target_for(
                contract_id,
                instance.sink_fn,
                10.0,
                ChainStrategy::DirectSink,
            ));
        }
        for direct in &self.direct_hints {
            targets.push(self.contract_target_for(
                direct.contract_id,
                direct.sink_fn,
                180.0,
                ChainStrategy::DirectSink,
            ));
        }
        for pair in &self.pairs {
            let next_fn = self
                .instances
                .get(pair.contract_id)
                .and_then(|instance| {
                    let called = self.has_called_contract_instance(builder, instance);
                    (!called).then_some(pair.producer_fn)
                })
                .unwrap_or(pair.sink_fn);
            targets.push(self.contract_target_for(
                pair.contract_id,
                next_fn,
                120.0,
                ChainStrategy::OneHop,
            ));
            targets.push(self.contract_target_for(
                pair.contract_id,
                pair.producer_fn,
                45.0,
                ChainStrategy::MultiHop,
            ));
        }
        for target in &self.public_field_targets {
            targets.push(self.contract_target_for(
                target.contract_id,
                target.sink_fn,
                220.0,
                ChainStrategy::OneHop,
            ));
        }
        for target in &self.hazard_targets {
            let Some(instance) = self.instances.get(target.contract_id) else {
                continue;
            };
            let (next_fn, priority) = if self.has_called_contract_instance(builder, instance) {
                (target.post_fn, 260.0)
            } else {
                (target.sink_fn, 160.0)
            };
            targets.push(self.contract_target_for(
                target.contract_id,
                next_fn,
                priority,
                ChainStrategy::HazardTemporal,
            ));
        }

        targets.sort_by_key(|target| {
            (
                target.contract_id,
                target.strategy,
                format!("{:?}", target.sink_fn),
            )
        });
        targets.dedup_by(|lhs, rhs| {
            lhs.contract_id == rhs.contract_id
                && lhs.strategy == rhs.strategy
                && lhs.sink_fn == rhs.sink_fn
        });
        targets
    }

    fn record_case_feedback(&mut self, metadata: &CaseMetadata) {
        self.chain_scheduler.record_case(metadata);
    }

    fn summary(&self, tcx: TyCtxt<'tcx>) -> String {
        let mut s = String::new();
        s.push_str(&format!(
            "contract: db_loaded={}, instances={}, effects={}, pairs={}, direct_hints={}, hazard_targets={}, hazard_temporal_plans={}, public_field_targets={}\n",
            self.contract_db_loaded,
            self.instances.len(),
            self.effects.len(),
            self.pairs.len(),
            self.direct_hints.len(),
            self.hazard_targets.len(),
            self.hazard_temporal_plans.len(),
            self.public_field_targets.len()
        ));
        s.push_str(&self.chain_scheduler.summary());

        if !self.instances.is_empty() {
            s.push_str("instances:\n");
            for instance in self.instances.iter().take(96) {
                s.push_str(&format!(
                    "  {}{} via {} ({:?}) requires {}({}) [{}]{} raw={}\n",
                    tcx.def_path_str(instance.sink_fn),
                    instance
                        .sink_self_ty
                        .as_ref()
                        .map(|ty| format!(" self_ty={ty}"))
                        .unwrap_or_default(),
                    instance.std_fn_name,
                    instance.std_fn,
                    instance.sp,
                    instance.args_display(tcx),
                    instance.usage.name(),
                    instance
                        .numeric_kind
                        .map(|kind| format!(" template={}", kind.name()))
                        .unwrap_or_default(),
                    instance.raw_tag
                ));
            }
        }

        if !self.effects.is_empty() {
            s.push_str("effects:\n");
            for effect in self.effects.iter().take(96) {
                s.push_str(&format!(
                    "  {}: {} on {}\n",
                    tcx.def_path_str(effect.fn_did),
                    effect.kind.name(),
                    symbolic_place_display(tcx, effect.adt_def, effect.kind.primary_place())
                ));
            }
        }

        if !self.pairs.is_empty() {
            s.push_str("pairs:\n");
            for pair in self.pairs.iter().take(96) {
                let pair_adt_def = self
                    .instances
                    .get(pair.contract_id)
                    .and_then(|instance| instance.adt_def)
                    .or_else(|| get_adt_def_id_by_adt_method(tcx, pair.producer_fn));
                s.push_str(&format!(
                    "  {} -> {} on {} via {} violates {} ({})\n",
                    tcx.def_path_str(pair.producer_fn),
                    tcx.def_path_str(pair.sink_fn),
                    symbolic_place_display(tcx, pair_adt_def, &pair.place),
                    pair.effect_kind,
                    pair.sp,
                    pair.reason
                ));
            }
        }

        if !self.direct_hints.is_empty() {
            s.push_str("direct hints:\n");
            for direct in self.direct_hints.iter().take(96) {
                s.push_str(&format!(
                    "  {} arg{} ({})\n",
                    tcx.def_path_str(direct.sink_fn),
                    direct.param_idx,
                    direct.reason
                ));
            }
        }

        if !self.hazard_targets.is_empty() {
            s.push_str("hazard targets:\n");
            for target in self.hazard_targets.iter().take(96) {
                s.push_str(&format!(
                    "  {} -> {} after sink on {} violates {} ({})\n",
                    tcx.def_path_str(target.sink_fn),
                    tcx.def_path_str(target.post_fn),
                    symbolic_place_display(
                        tcx,
                        self.instances
                            .get(target.contract_id)
                            .and_then(|instance| instance.adt_def),
                        &target.place
                    ),
                    target.sp,
                    target.reason
                ));
            }
        }

        if !self.public_field_targets.is_empty() {
            s.push_str("public field targets:\n");
            for target in self.public_field_targets.iter().take(96) {
                s.push_str(&format!(
                    "  {}.{} -> {} violates {} ({})\n",
                    tcx.def_path_str(target.adt_def),
                    target.field_name,
                    tcx.def_path_str(target.sink_fn),
                    target.sp,
                    target.reason
                ));
            }
        }

        if !self.hazard_temporal_plans.is_empty() {
            s.push_str("hazard temporal plans:\n");
            for plan in self.hazard_temporal_plans.iter().take(96) {
                s.push_str(&format!(
                    "  contract#{} {} -> {} -> {:?}\n",
                    plan.contract_id, plan.source_fn, plan.invalidator_fn, plan.observer
                ));
            }
        }

        s
    }
}

fn merge_hints(lhs: Vec<Option<InputHint>>, rhs: Vec<Option<InputHint>>) -> Vec<Option<InputHint>> {
    let mut res = lhs;
    if rhs.len() > res.len() {
        res.resize(rhs.len(), None);
    }
    for (idx, hint) in rhs.into_iter().enumerate() {
        if res[idx].is_none() {
            res[idx] = hint;
        }
    }
    res
}

fn attrs(entries: &[(&str, String)]) -> BTreeMap<String, String> {
    entries
        .iter()
        .map(|(key, value)| ((*key).to_owned(), value.clone()))
        .collect()
}

fn insert_ccag_node(
    nodes: &mut BTreeMap<String, CcagNodeRecord>,
    id: String,
    kind: impl Into<String>,
    label: impl Into<String>,
    attrs: BTreeMap<String, String>,
) {
    nodes.entry(id.clone()).or_insert(CcagNodeRecord {
        id,
        kind: kind.into(),
        label: label.into(),
        attrs,
    });
}

fn ccag_edge(
    source: String,
    target: String,
    kind: impl Into<String>,
    label: impl Into<String>,
    attrs: BTreeMap<String, String>,
) -> CcagEdgeRecord {
    CcagEdgeRecord {
        source,
        target,
        kind: kind.into(),
        label: label.into(),
        attrs,
    }
}

fn action_api_node_id(def_id: DefId) -> String {
    format!("action:api:{def_id:?}")
}

fn place_node_id(place: &SymbolicPlace) -> String {
    format!("field:{}", place.pretty())
}

fn field_root_name(root: PlaceRoot) -> String {
    match root {
        PlaceRoot::Return => "return".to_owned(),
        PlaceRoot::Receiver => "self".to_owned(),
        PlaceRoot::Param(idx) => format!("arg{idx}"),
        PlaceRoot::Local(idx) => format!("local{idx}"),
    }
}

fn symbolic_place_display(
    tcx: TyCtxt<'_>,
    receiver_adt_def: Option<DefId>,
    place: &SymbolicPlace,
) -> String {
    let root = field_root_name(place.root);
    if place.fields.is_empty() {
        return root;
    }

    if matches!(place.root, PlaceRoot::Receiver) {
        if let Some(adt_def) = receiver_adt_def {
            if let Some(path) = field_path_name(tcx, adt_def, &place.fields) {
                return format!("{root}.{path}");
            }
        }
    }

    format!(
        "{}.{}",
        root,
        place.fields.iter().map(|field| field.to_string()).join(".")
    )
}

fn insert_state_field_path(
    tcx: TyCtxt<'_>,
    nodes: &mut BTreeMap<String, CcagNodeRecord>,
    edges: &mut Vec<CcagEdgeRecord>,
    place: &SymbolicPlace,
    receiver_adt_def: Option<DefId>,
) -> String {
    let mut current = SymbolicPlace {
        root: place.root,
        fields: Vec::new(),
    };
    let root_id = place_node_id(&current);
    let root_label = symbolic_place_display(tcx, receiver_adt_def, &current);
    insert_ccag_node(
        nodes,
        root_id.clone(),
        "state_field",
        root_label.clone(),
        attrs(&[
            ("root", field_root_name(current.root)),
            ("field_path", "[]".to_owned()),
            ("display", root_label),
        ]),
    );

    let mut parent_id = root_id;
    for field in &place.fields {
        current.fields.push(*field);
        let current_id = place_node_id(&current);
        let current_label = symbolic_place_display(tcx, receiver_adt_def, &current);
        insert_ccag_node(
            nodes,
            current_id.clone(),
            "state_field",
            current_label.clone(),
            attrs(&[
                ("root", field_root_name(current.root)),
                ("field_path", format!("{:?}", current.fields)),
                ("display", current_label),
            ]),
        );
        edges.push(ccag_edge(
            parent_id,
            current_id.clone(),
            "contains",
            "contains",
            BTreeMap::new(),
        ));
        parent_id = current_id;
    }

    parent_id
}

fn implicit_contract_place(contract_id: usize) -> SymbolicPlace {
    SymbolicPlace {
        root: PlaceRoot::Local(10_000 + contract_id),
        fields: Vec::new(),
    }
}

fn public_field_action_node_id(target: &PublicFieldTarget) -> String {
    format!(
        "action:public-field:{:?}:{}:{}",
        target.adt_def, target.field_name, target.contract_id
    )
}

fn recipe_action_node_id(contract_id: usize, hint_kind: &str) -> String {
    format!("action:recipe:{contract_id}:{hint_kind}")
}

fn ref_source_map<'tcx>(stmts: &[Stmt<'tcx>]) -> HashMap<Var, Var> {
    let mut ref_source = HashMap::new();
    for stmt in stmts {
        if let StmtKind::Ref(source, _) | StmtKind::SliceRef(source, _) = stmt.kind() {
            ref_source.insert(stmt.place(), *source);
        }
    }
    ref_source
}

fn normalize_ref_var(mut var: Var, ref_source: &HashMap<Var, Var>) -> Var {
    while let Some(source) = ref_source.get(&var).copied() {
        var = source;
    }
    var
}

fn field_path_name(tcx: TyCtxt<'_>, root_adt_def: DefId, field_path: &[usize]) -> Option<String> {
    let mut adt_def = tcx.adt_def(root_adt_def);
    let mut args = ty::GenericArgs::identity_for_item(tcx, root_adt_def);
    let mut names = Vec::new();

    for (idx, field_index) in field_path.iter().copied().enumerate() {
        if !adt_def.is_struct() {
            return None;
        }
        let field = adt_def.non_enum_variant().fields.iter().nth(field_index)?;
        names.push(field.name.to_string());
        if idx + 1 == field_path.len() {
            break;
        }

        let field_ty = field.ty(tcx, args);
        let TyKind::Adt(next_adt, next_args) = field_ty.kind() else {
            return None;
        };
        adt_def = *next_adt;
        args = *next_args;
    }

    Some(names.join("."))
}

fn public_field_path_name(
    tcx: TyCtxt<'_>,
    root_adt_def: DefId,
    field_path: &[usize],
) -> Option<String> {
    let mut adt_def = tcx.adt_def(root_adt_def);
    let mut args = ty::GenericArgs::identity_for_item(tcx, root_adt_def);
    let mut names = Vec::new();

    for (idx, field_index) in field_path.iter().copied().enumerate() {
        if !adt_def.is_struct() {
            return None;
        }
        let field = adt_def.non_enum_variant().fields.iter().nth(field_index)?;
        if !tcx.visibility(field.did).is_public() {
            return None;
        }
        names.push(field.name.to_string());
        if idx + 1 == field_path.len() {
            break;
        }

        let field_ty = field.ty(tcx, args);
        let TyKind::Adt(next_adt, next_args) = field_ty.kind() else {
            return None;
        };
        adt_def = *next_adt;
        args = *next_args;
    }

    Some(names.join("."))
}

fn is_public_field(tcx: TyCtxt<'_>, adt_def: DefId, field_index: usize) -> bool {
    let adt = tcx.adt_def(adt_def);
    if !adt.is_struct() {
        return false;
    }
    adt.non_enum_variant()
        .fields
        .iter()
        .nth(field_index)
        .map(|field| tcx.visibility(field.did).is_public())
        .unwrap_or(false)
}

fn field_ty_for_base<'tcx>(
    tcx: TyCtxt<'tcx>,
    builder: &ContextBuilder<'tcx, '_>,
    base: Var,
    target: &PublicFieldTarget,
) -> Option<Ty<'tcx>> {
    let base_ty = builder.cx().type_of(base);
    let (adt_def, args) = match base_ty.kind() {
        ty::Adt(adt_def, args) if adt_def.did() == target.adt_def => (*adt_def, *args),
        ty::Adt(box_def, box_args) if tcx.is_lang_item(box_def.did(), LangItem::OwnedBox) => {
            let inner_ty = box_args.type_at(0);
            let ty::Adt(inner_adt, inner_args) = inner_ty.kind() else {
                return None;
            };
            if inner_adt.did() != target.adt_def {
                return None;
            }
            (*inner_adt, *inner_args)
        }
        ty::Ref(_, inner_ty, _) => {
            let ty::Adt(adt_def, args) = inner_ty.kind() else {
                return None;
            };
            if adt_def.did() != target.adt_def {
                return None;
            }
            (*adt_def, *args)
        }
        _ => return None,
    };
    field_ty_for_path(tcx, adt_def.did(), args, &target.field_path)
}

fn field_ty_for_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    root_adt_def: DefId,
    root_args: ty::GenericArgsRef<'tcx>,
    field_path: &[usize],
) -> Option<Ty<'tcx>> {
    let mut adt_def = tcx.adt_def(root_adt_def);
    let mut args = root_args;
    let mut ty = None;

    for field_index in field_path {
        if !adt_def.is_struct() {
            return None;
        }
        let field = adt_def.non_enum_variant().fields.iter().nth(*field_index)?;
        let field_ty = field.ty(tcx, args);
        ty = Some(field_ty);

        if let TyKind::Adt(next_adt, next_args) = field_ty.kind() {
            adt_def = *next_adt;
            args = *next_args;
        }
    }

    ty
}

fn output_constructs_adt(ty: Ty<'_>, adt_def_id: DefId) -> bool {
    match ty.kind() {
        TyKind::Adt(adt_def, _) => adt_def.did() == adt_def_id,
        _ => false,
    }
}

fn output_adt_def_id(ty: Ty<'_>) -> Option<DefId> {
    match ty.kind() {
        TyKind::Adt(adt_def, _) => Some(adt_def.did()),
        _ => None,
    }
}

fn sink_signature(tcx: TyCtxt<'_>, sink_fn: DefId) -> String {
    format!("{:?}", tcx.fn_sig(sink_fn))
}

fn sink_self_ty(tcx: TyCtxt<'_>, sink_fn: DefId) -> Option<String> {
    let sig = tcx.fn_sig(sink_fn).skip_binder();
    sig.inputs().skip_binder().first().map(|ty| ty.to_string())
}

fn is_alignment_contract(instance: &ContractInstance) -> bool {
    matches!(
        instance.sp,
        PrimitiveSpKind::Align | PrimitiveSpKind::DoubleAlign
    )
}

fn generic_preference_for_instance(instance: &ContractInstance) -> ContractGenericPreference {
    if is_alignment_contract(instance) && instance.sink_requires_monomorphization {
        ContractGenericPreference::HighAlignment
    } else {
        ContractGenericPreference::Any
    }
}

fn call_matches_contract_instance<'tcx>(instance: &ContractInstance, call: &ApiCall<'tcx>) -> bool {
    if call.fn_did() != instance.sink_fn {
        return false;
    }
    match generic_preference_for_instance(instance) {
        ContractGenericPreference::Any => true,
        ContractGenericPreference::HighAlignment => {
            high_alignment_generic_score(call.generic_args()) > 0.0
        }
    }
}

fn high_alignment_generic_score(args: GenericArgsRef<'_>) -> f32 {
    let score = args
        .iter()
        .filter_map(|arg| arg.as_type())
        .map(high_alignment_ty_score)
        .fold(0.0, f32::max);
    if score > 0.0 {
        return score;
    }

    let rendered = format!("{args:?}");
    if rendered.contains("i128")
        || rendered.contains("u128")
        || rendered.contains("I128")
        || rendered.contains("U128")
    {
        1.0
    } else if rendered.contains("i64")
        || rendered.contains("u64")
        || rendered.contains("isize")
        || rendered.contains("usize")
        || rendered.contains("f64")
        || rendered.contains("I64")
        || rendered.contains("U64")
    {
        0.5
    } else {
        0.0
    }
}

fn high_alignment_ty_score(ty: Ty<'_>) -> f32 {
    let score = match ty.kind() {
        TyKind::Int(IntTy::I128) | TyKind::Uint(UintTy::U128) => 1.0,
        TyKind::Int(IntTy::I64)
        | TyKind::Uint(UintTy::U64)
        | TyKind::Int(IntTy::Isize)
        | TyKind::Uint(UintTy::Usize)
        | TyKind::Float(FloatTy::F64) => 0.5,
        TyKind::Array(inner, _) | TyKind::Slice(inner) => high_alignment_ty_score(*inner),
        TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => high_alignment_ty_score(*inner),
        TyKind::Adt(_, args) => high_alignment_generic_score(args),
        _ => 0.0,
    };
    if score > 0.0 {
        return score;
    }

    match ty.to_string().as_str() {
        "i128" | "u128" => 1.0,
        "i64" | "u64" | "isize" | "usize" | "f64" => 0.5,
        _ => 0.0,
    }
}

fn collect_public_field_targets<'tcx>(
    tcx: TyCtxt<'tcx>,
    instances: &[ContractInstance],
) -> Vec<PublicFieldTarget> {
    let mut targets = Vec::new();

    for (contract_id, instance) in instances.iter().enumerate() {
        if !matches!(
            instance.usage,
            ContractUsage::Precondition | ContractUsage::Unknown
        ) {
            continue;
        }
        let Some(adt_def) = instance.adt_def else {
            continue;
        };
        for place in instance
            .sensitive_place()
            .into_iter()
            .filter(|place| place.is_receiver_field())
        {
            let field_index = place.fields[0];
            if !is_public_field(tcx, adt_def, field_index) {
                continue;
            }
            let Some(field_name) = public_field_path_name(tcx, adt_def, &place.fields) else {
                continue;
            };
            let reason = format!(
                "public field {}.{} can break {} required by {}",
                tcx.def_path_str(adt_def),
                field_name,
                instance.sp,
                instance.std_fn_name
            );
            targets.push(PublicFieldTarget {
                contract_id,
                sink_fn: instance.sink_fn,
                adt_def,
                field_path: place.fields.clone(),
                field_name,
                place: place.clone(),
                sp: instance.sp.clone(),
                hint: instance.invalid_hint(reason.clone()),
                reason,
            });
        }
    }

    targets.sort_by_key(|target| {
        (
            format!("{:?}", target.sink_fn),
            target.contract_id,
            target.field_path.clone(),
        )
    });
    targets.dedup_by(|lhs, rhs| {
        lhs.contract_id == rhs.contract_id
            && lhs.sink_fn == rhs.sink_fn
            && lhs.adt_def == rhs.adt_def
            && lhs.field_path == rhs.field_path
    });
    targets
}

const LOCAL_CONTRACT_BINDINGS_ENV: &str = "TESTGEN_CONTRACT_BINDINGS";
const LOCAL_CONTRACT_BINDINGS_FILE: &str = "testgen_contract_bindings.json";

fn load_std_contract_bindings() -> HashMap<String, Vec<StdContractBinding>> {
    serde_json::from_str(include_str!("data/std_contract_bindings.json"))
        .expect("Unable to parse std contract bindings")
}

fn load_contract_bindings(
    tcx: TyCtxt<'_>,
    candidate_fns: &[DefId],
) -> HashMap<String, Vec<StdContractBinding>> {
    let mut bindings = load_std_contract_bindings();
    let local_paths = local_contract_binding_paths(tcx, candidate_fns);
    if env::var("TESTGEN_DEBUG_CONTRACT_BINDINGS").is_ok() {
        rap_info!(
            "contract guide: local contract binding candidates: {}",
            local_paths.iter().map(|path| path.display()).join(", ")
        );
    }
    for path in local_paths {
        if !path.exists() {
            continue;
        }
        let input = fs::read_to_string(&path).unwrap_or_else(|err| {
            panic!(
                "Unable to read local testgen contract bindings from {}: {err}",
                path.display()
            )
        });
        let local: HashMap<String, Vec<StdContractBinding>> = serde_json::from_str(&input)
            .unwrap_or_else(|err| {
                panic!(
                    "Unable to parse local testgen contract bindings from {}: {err}",
                    path.display()
                )
            });
        rap_info!(
            "contract guide: loaded local contract bindings from {}",
            path.display()
        );
        for (function, mut entries) in local {
            bindings.entry(function).or_default().append(&mut entries);
        }
    }
    bindings
}

fn local_contract_binding_paths(tcx: TyCtxt<'_>, candidate_fns: &[DefId]) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    if let Ok(path) = env::var(LOCAL_CONTRACT_BINDINGS_ENV) {
        push_unique_path(&mut paths, PathBuf::from(path));
        return paths;
    }

    if let Ok(current_dir) = env::current_dir() {
        push_local_contract_binding_ancestors(&mut paths, &current_dir);
    }
    if let Ok(manifest_dir) = env::var("CARGO_MANIFEST_DIR") {
        push_local_contract_binding_ancestors(&mut paths, Path::new(&manifest_dir));
    }
    push_source_contract_binding_ancestors(&mut paths, tcx, candidate_fns);
    paths
}

fn push_local_contract_binding_ancestors(paths: &mut Vec<PathBuf>, start: &Path) {
    for ancestor in start.ancestors() {
        push_unique_path(paths, ancestor.join(LOCAL_CONTRACT_BINDINGS_FILE));
    }
}

fn push_unique_path(paths: &mut Vec<PathBuf>, path: PathBuf) {
    let normalized = path.canonicalize().unwrap_or_else(|_| path.clone());
    let already_present = paths
        .iter()
        .any(|existing| existing.canonicalize().unwrap_or_else(|_| existing.clone()) == normalized);
    if !already_present {
        paths.push(path);
    }
}

fn push_source_contract_binding_ancestors(
    paths: &mut Vec<PathBuf>,
    tcx: TyCtxt<'_>,
    candidate_fns: &[DefId],
) {
    let source_map = tcx.sess.source_map();
    for &fn_did in candidate_fns {
        if !fn_did.is_local() {
            continue;
        }
        let FileName::Real(real_path) = source_map.span_to_filename(tcx.def_span(fn_did)) else {
            continue;
        };
        let path = PathBuf::from(
            real_path
                .to_string_lossy(FileNameDisplayPreference::Local)
                .into_owned(),
        );
        if let Some(parent) = path.parent() {
            push_local_contract_binding_ancestors(paths, parent);
        }
    }
}

fn contract_stable_id(tcx: TyCtxt<'_>, id: usize, instance: &ContractInstance) -> String {
    contract_edge_id(tcx, id, instance)
}

fn contract_edge_id(tcx: TyCtxt<'_>, id: usize, instance: &ContractInstance) -> String {
    format!(
        "contract-edge:{id}:{}:{}:{}",
        instance.sp,
        tcx.def_path_str(instance.sink_fn),
        instance.std_fn_name
    )
}

fn std_contract_callee_name(tcx: TyCtxt<'_>, callee_def_id: DefId) -> Option<String> {
    let raw = format!("{:?}", callee_def_id);
    if raw.contains("~ core[") || raw.contains("~ std[") || raw.contains("~ alloc[") {
        Some(get_cleaned_def_path_name(tcx, callee_def_id))
    } else {
        None
    }
}

fn contract_callee_name(
    tcx: TyCtxt<'_>,
    callee_def_id: DefId,
    contract_db: &SafetyContractDb,
    contract_bindings: &HashMap<String, Vec<StdContractBinding>>,
) -> Option<String> {
    if let Some(std_name) = std_contract_callee_name(tcx, callee_def_id) {
        return Some(std_name);
    }

    let local_name = tcx.def_path_str(callee_def_id);
    if let Some(contract_key) = matching_contract_db_key(contract_db, &local_name) {
        Some(contract_key)
    } else if let Some(binding_key) = matching_contract_binding_key(contract_bindings, &local_name)
    {
        Some(binding_key)
    } else {
        if env::var("TESTGEN_DEBUG_CONTRACT_BINDINGS").is_ok() {
            rap_info!("contract guide: local callee has no contract binding: {local_name}");
        }
        None
    }
}

fn contract_key_matches(callee_name: &str, contract_key: &str) -> bool {
    callee_name == contract_key
        || callee_name
            .strip_suffix(contract_key)
            .is_some_and(|prefix| prefix.ends_with("::"))
        || contract_key
            .strip_suffix(callee_name)
            .is_some_and(|prefix| prefix.ends_with("::"))
}

fn matching_contract_db_key(contract_db: &SafetyContractDb, callee_name: &str) -> Option<String> {
    if contract_db.get(callee_name).is_some() {
        return Some(callee_name.to_owned());
    }
    contract_db
        .iter()
        .find(|(function, _)| contract_key_matches(callee_name, function))
        .map(|(function, _)| function.to_owned())
}

fn matching_contract_binding_key(
    contract_bindings: &HashMap<String, Vec<StdContractBinding>>,
    callee_name: &str,
) -> Option<String> {
    if contract_bindings.contains_key(callee_name) {
        return Some(callee_name.to_owned());
    }
    contract_bindings
        .keys()
        .find(|function| contract_key_matches(callee_name, function))
        .cloned()
}

fn callee_has_contract(
    contract_db: &SafetyContractDb,
    contract_bindings: &HashMap<String, Vec<StdContractBinding>>,
    callee_name: &str,
) -> bool {
    contract_db.get(callee_name).is_some()
        || contract_bindings.get(callee_name).is_some_and(|bindings| {
            bindings
                .iter()
                .any(|binding| binding.contract_spec().is_some())
        })
}

fn binding_contract_specs(bindings: &[StdContractBinding]) -> Vec<BindingContractSpec> {
    bindings
        .iter()
        .filter_map(StdContractBinding::contract_spec)
        .collect()
}

fn should_lift_binding_contract_spec(has_db_contract: bool, spec: &BindingContractSpec) -> bool {
    !(has_db_contract && matches!(spec.usage, ContractUsage::Precondition))
}

fn collect_lifted_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    contract_db: &SafetyContractDb,
    dataflow_graphs: &LazyDataFlowGraphs<'tcx>,
    candidate_fns: &[DefId],
) -> Vec<ContractInstance> {
    let contract_bindings = load_contract_bindings(tcx, candidate_fns);
    let mut instances = Vec::new();

    for &fn_did in candidate_fns {
        if !is_local_mir_fn(tcx, fn_did) {
            continue;
        }
        let adt_def = get_adt_def_id_by_adt_method(tcx, fn_did);
        let body = tcx.optimized_mir(fn_did);
        let has_contract_call = body.basic_blocks.iter().any(|block| {
            let terminator = block.terminator();
            let TerminatorKind::Call { func, .. } = &terminator.kind else {
                return false;
            };
            let Some(callee_def_id) = operand_fn_def(func) else {
                return false;
            };
            let Some(callee_name) =
                contract_callee_name(tcx, callee_def_id, contract_db, &contract_bindings)
            else {
                return false;
            };
            callee_has_contract(contract_db, &contract_bindings, &callee_name)
        });
        if !has_contract_call {
            continue;
        }
        let mut resolver = PlaceResolver::for_fn(tcx, fn_did, Some(dataflow_graphs));
        for block in body.basic_blocks.iter() {
            for stmt in block.statements.iter() {
                collect_alias_from_statement(tcx, fn_did, &mut resolver, &stmt.kind);
            }
            let terminator = block.terminator();
            let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                continue;
            };
            let Some(callee_def_id) = operand_fn_def(func) else {
                continue;
            };
            let Some(callee_name) =
                contract_callee_name(tcx, callee_def_id, contract_db, &contract_bindings)
            else {
                continue;
            };
            let bindings = contract_bindings.get(&callee_name);
            let mut lifted_specs = BTreeSet::new();
            let has_db_contract = contract_db.get(&callee_name).is_some();
            if let Some(contract) = contract_db.get(&callee_name) {
                for properties in contract.sites().values() {
                    for property in properties {
                        lifted_specs.insert((
                            property.kind().to_string(),
                            property.raw_tag().to_owned(),
                            default_contract_usage_for_sp(property.kind())
                                .name()
                                .to_owned(),
                        ));
                        instances.extend(lift_property_instances(
                            tcx,
                            fn_did,
                            adt_def,
                            callee_def_id,
                            &callee_name,
                            property.raw_tag(),
                            property.kind().clone(),
                            default_contract_usage_for_sp(property.kind()),
                            bindings.map(Vec::as_slice).unwrap_or(&[]),
                            args,
                            &resolver,
                        ));
                    }
                }
            }
            if let Some(bindings) = bindings {
                for spec in binding_contract_specs(bindings) {
                    if !should_lift_binding_contract_spec(has_db_contract, &spec) {
                        continue;
                    }
                    if !lifted_specs.insert((
                        spec.sp.to_string(),
                        spec.raw_tag.clone(),
                        spec.usage.name().to_owned(),
                    )) {
                        continue;
                    }
                    instances.extend(lift_property_instances(
                        tcx,
                        fn_did,
                        adt_def,
                        callee_def_id,
                        &callee_name,
                        &spec.raw_tag,
                        spec.sp,
                        spec.usage,
                        bindings,
                        args,
                        &resolver,
                    ));
                }
            }
        }
    }

    instances
}

fn lift_property_instances<'tcx>(
    tcx: TyCtxt<'tcx>,
    sink_fn: DefId,
    adt_def: Option<DefId>,
    std_fn: DefId,
    std_fn_name: &str,
    raw_tag: &str,
    sp: PrimitiveSpKind,
    fallback_usage: ContractUsage,
    bindings: &[StdContractBinding],
    args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
    resolver: &PlaceResolver,
) -> Vec<ContractInstance> {
    let mut instances = Vec::new();

    for binding in bindings.iter().filter(|binding| binding.matches_sp(&sp)) {
        let Some(symbolic_args) = lift_contract_binding_args(tcx, sink_fn, binding, args, resolver)
        else {
            continue;
        };
        instances.push(ContractInstance {
            sink_fn,
            adt_def,
            sink_self_ty: sink_self_ty(tcx, sink_fn),
            sink_signature: sink_signature(tcx, sink_fn),
            sink_requires_monomorphization: tcx.generics_of(sink_fn).requires_monomorphization(tcx),
            std_fn,
            std_fn_name: std_fn_name.to_owned(),
            sp: sp.clone(),
            raw_tag: raw_tag.to_owned(),
            symbolic_args,
            usage: binding.usage(),
            numeric_kind: binding.numeric_kind(),
            binding_role: binding.role().map(str::to_owned),
        });
    }

    if !instances.is_empty() {
        return instances;
    }

    let symbolic_args = resolve_all_symbolic_args(tcx, sink_fn, args, resolver);
    if symbolic_args.is_empty() {
        return instances;
    }

    instances.push(ContractInstance {
        sink_fn,
        adt_def,
        sink_self_ty: sink_self_ty(tcx, sink_fn),
        sink_signature: sink_signature(tcx, sink_fn),
        sink_requires_monomorphization: tcx.generics_of(sink_fn).requires_monomorphization(tcx),
        std_fn,
        std_fn_name: std_fn_name.to_owned(),
        sp,
        raw_tag: raw_tag.to_owned(),
        symbolic_args,
        usage: fallback_usage,
        numeric_kind: None,
        binding_role: None,
    });
    instances
}

fn lift_contract_binding_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    binding: &StdContractBinding,
    args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
    resolver: &PlaceResolver,
) -> Option<Vec<SymbolicPlace>> {
    let resolve = |idx| resolve_arg_symbolic(tcx, fn_did, args, idx, resolver);
    binding
        .arg_indices()
        .into_iter()
        .map(|idx| resolve(idx))
        .collect::<Option<Vec<_>>>()
}

fn resolve_all_symbolic_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
    resolver: &PlaceResolver,
) -> Vec<SymbolicPlace> {
    args.iter()
        .filter_map(|arg| resolver.resolve_operand(tcx, fn_did, &arg.node))
        .collect()
}

fn collect_effects<'tcx>(
    tcx: TyCtxt<'tcx>,
    dataflow_graphs: &LazyDataFlowGraphs<'tcx>,
    candidate_fns: &[DefId],
) -> Vec<ContractEffect> {
    let mut effects = Vec::new();
    for &fn_did in candidate_fns {
        if !is_local_mir_fn(tcx, fn_did) {
            continue;
        }
        let adt_def = get_adt_def_id_by_adt_method(tcx, fn_did);
        collect_constructor_effect(tcx, fn_did, dataflow_graphs, &mut effects);
        let body = tcx.optimized_mir(fn_did);
        let mut resolver = PlaceResolver::for_fn(tcx, fn_did, Some(dataflow_graphs));
        for block in body.basic_blocks.iter() {
            for stmt in block.statements.iter() {
                collect_alias_from_statement(tcx, fn_did, &mut resolver, &stmt.kind);
                collect_assignment_effect(
                    tcx,
                    fn_did,
                    adt_def,
                    &resolver,
                    &stmt.kind,
                    &mut effects,
                );
            }

            let terminator = block.terminator();
            let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                continue;
            };
            let Some(callee_def_id) = operand_fn_def(func) else {
                continue;
            };
            let callee_name = get_cleaned_def_path_name(tcx, callee_def_id);
            collect_call_effects(
                tcx,
                fn_did,
                adt_def,
                &callee_name,
                args,
                &resolver,
                &mut effects,
            );
        }
    }
    effects
}

fn collect_constructor_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    dataflow_graphs: &LazyDataFlowGraphs<'tcx>,
    effects: &mut Vec<ContractEffect>,
) {
    let sig = tcx.fn_sig(fn_did).skip_binder();
    let output_ty = sig.output().skip_binder();
    let Some(output_adt) = output_adt_def_id(output_ty) else {
        return;
    };
    if tcx.is_lang_item(output_adt, LangItem::OwnedBox) {
        return;
    }

    effects.push(ContractEffect {
        fn_did,
        adt_def: Some(output_adt),
        kind: EffectKind::ConstructAdt {
            output: SymbolicPlace {
                root: PlaceRoot::Return,
                fields: Vec::new(),
            },
            inputs: Vec::new(),
        },
        confidence: EffectConfidence::Approximate,
    });

    let body = tcx.optimized_mir(fn_did);
    let mut resolver = PlaceResolver::for_fn(tcx, fn_did, Some(dataflow_graphs));
    for block in body.basic_blocks.iter() {
        for stmt in block.statements.iter() {
            collect_alias_from_statement(tcx, fn_did, &mut resolver, &stmt.kind);
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (lhs, rvalue) = &**assign;
            let Some(output) = raw_symbolic_place(tcx, fn_did, lhs) else {
                continue;
            };
            if !matches!(output.root, PlaceRoot::Return) || output.fields.is_empty() {
                continue;
            }
            let inputs = symbolic_places_from_rvalue(tcx, fn_did, rvalue, &resolver);
            effects.push(ContractEffect {
                fn_did,
                adt_def: Some(output_adt),
                kind: EffectKind::ConstructAdt { output, inputs },
                confidence: EffectConfidence::Flow,
            });
        }
    }
}

fn collect_assignment_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    adt_def: Option<DefId>,
    resolver: &PlaceResolver,
    stmt: &StatementKind<'tcx>,
    effects: &mut Vec<ContractEffect>,
) {
    let StatementKind::Assign(assign) = stmt else {
        return;
    };
    let (lhs, rvalue) = &**assign;
    let Some(field) = resolver.resolve_place(tcx, fn_did, lhs) else {
        return;
    };
    if !field.is_receiver_field() {
        return;
    }
    let value = effect_value_from_rvalue(tcx, fn_did, rvalue, resolver);
    let inputs = symbolic_places_from_rvalue(tcx, fn_did, rvalue, resolver);
    effects.push(ContractEffect {
        fn_did,
        adt_def,
        kind: EffectKind::WriteField {
            field,
            value,
            inputs,
        },
        confidence: EffectConfidence::Exact,
    });
}

fn collect_call_effects<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    adt_def: Option<DefId>,
    callee_name: &str,
    args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
    resolver: &PlaceResolver,
    effects: &mut Vec<ContractEffect>,
) {
    let Some(first_place) = resolve_arg_symbolic(tcx, fn_did, args, 0, resolver) else {
        return;
    };

    if callee_name.ends_with("::set_len") {
        let value = args
            .get(1)
            .map(|arg| effect_value_from_operand(tcx, fn_did, &arg.node, resolver))
            .unwrap_or(EffectValue::Unknown);
        effects.push(ContractEffect {
            fn_did,
            adt_def,
            kind: EffectKind::SetLen {
                place: first_place,
                value,
            },
            confidence: EffectConfidence::Exact,
        });
    } else if callee_name.ends_with("::as_mut_vec") || callee_name.ends_with("::as_bytes_mut") {
        effects.push(ContractEffect {
            fn_did,
            adt_def,
            kind: EffectKind::InvalidateUtf8 { place: first_place },
            confidence: EffectConfidence::Approximate,
        });
    } else if is_free_allocation_call(callee_name) {
        effects.push(ContractEffect {
            fn_did,
            adt_def,
            kind: EffectKind::FreeAllocation { place: first_place },
            confidence: EffectConfidence::Approximate,
        });
    } else if callee_name.contains("::assume_init") {
        effects.push(ContractEffect {
            fn_did,
            adt_def,
            kind: EffectKind::AssumeInit { place: first_place },
            confidence: EffectConfidence::Approximate,
        });
    }
}

fn is_free_allocation_call(callee_name: &str) -> bool {
    callee_name.contains("::dealloc")
        || (callee_name.contains("::from_raw") && !callee_name.contains("from_raw_parts"))
}

fn build_conflicts(
    tcx: TyCtxt<'_>,
    instances: &[ContractInstance],
    effects: &[ContractEffect],
) -> (Vec<ConflictPair>, Vec<DirectSinkHint>, Vec<HazardTarget>) {
    let mut pairs = Vec::new();
    let mut direct_hints = Vec::new();
    let mut hazard_targets = Vec::new();

    for (contract_id, instance) in instances.iter().enumerate() {
        if matches!(instance.usage, ContractUsage::Option) {
            continue;
        }

        if matches!(instance.usage, ContractUsage::Hazard) {
            for effect in effects {
                if effect.fn_did == instance.sink_fn {
                    continue;
                }
                if instance.adt_def.is_some() && effect.adt_def != instance.adt_def {
                    continue;
                }
                if !effect_may_violate_contract(effect, instance) {
                    continue;
                }
                let place = effect.kind.primary_place().clone();
                let place_display =
                    symbolic_place_display(tcx, effect.adt_def.or(instance.adt_def), &place);
                let reason = format!(
                    "post-call {} on {} can trigger {} hazard created by {}",
                    effect.kind.name(),
                    place_display,
                    instance.sp,
                    instance.std_fn_name
                );
                hazard_targets.push(HazardTarget {
                    contract_id,
                    sink_fn: instance.sink_fn,
                    post_fn: effect.fn_did,
                    place,
                    sp: instance.sp.clone(),
                    effect_kind: effect.kind.name(),
                    effect_confidence: effect.confidence.name(),
                    reason,
                });
            }
            continue;
        }

        let direct_hint_params = if matches!(instance.sp, PrimitiveSpKind::NonOverlap) {
            instance
                .symbolic_args
                .iter()
                .filter_map(SymbolicPlace::is_param)
                .collect_vec()
        } else {
            instance
                .sensitive_place()
                .and_then(SymbolicPlace::is_param)
                .into_iter()
                .collect_vec()
        };
        for param_idx in direct_hint_params {
            let reason = format!("{} contract of {}", instance.sp, instance.std_fn_name);
            if let Some(hint) = instance.invalid_hint(reason.clone()) {
                direct_hints.push(DirectSinkHint {
                    contract_id,
                    sink_fn: instance.sink_fn,
                    param_idx,
                    hint,
                    reason,
                });
            }
        }

        for effect in effects {
            if instance.adt_def.is_some() && effect.adt_def != instance.adt_def {
                continue;
            }
            if !effect_may_violate_contract(effect, instance) {
                continue;
            }
            let place = effect.kind.primary_place().clone();
            let flow_note = match &effect.kind {
                EffectKind::ConstructAdt { inputs, .. } if !inputs.is_empty() => {
                    format!(
                        " from {}",
                        inputs
                            .iter()
                            .map(|place| symbolic_place_display(tcx, effect.adt_def, place))
                            .join(", ")
                    )
                }
                _ => String::new(),
            };
            let place_display =
                symbolic_place_display(tcx, effect.adt_def.or(instance.adt_def), &place);
            let reason = format!(
                "{} on {} can break {} required by {}",
                effect.kind.name(),
                format!("{place_display}{flow_note}"),
                instance.sp,
                instance.std_fn_name
            );

            let (hint_param, hint) = match effect.kind.value() {
                Some(EffectValue::Param(param_idx)) => {
                    (Some(param_idx), instance.invalid_hint(reason.clone()))
                }
                Some(EffectValue::Const(value)) => {
                    if const_may_violate_instance(instance, value) {
                        (None, None)
                    } else {
                        continue;
                    }
                }
                Some(EffectValue::Unknown) | None => (None, None),
            };

            pairs.push(ConflictPair {
                contract_id,
                producer_fn: effect.fn_did,
                sink_fn: instance.sink_fn,
                place,
                sp: instance.sp.clone(),
                effect_kind: effect.kind.name(),
                effect_confidence: effect.confidence.name(),
                hint_param,
                hint,
                reason,
            });
        }
    }

    pairs.sort_by_key(|pair| {
        (
            format!("{:?}", pair.producer_fn),
            format!("{:?}", pair.sink_fn),
            pair.contract_id,
            pair.place.pretty(),
            pair.sp.to_string(),
            pair.hint_param,
        )
    });
    pairs.dedup_by(|lhs, rhs| {
        lhs.producer_fn == rhs.producer_fn
            && lhs.sink_fn == rhs.sink_fn
            && lhs.contract_id == rhs.contract_id
            && lhs.place == rhs.place
            && lhs.sp == rhs.sp
            && lhs.hint_param == rhs.hint_param
    });

    direct_hints.sort_by_key(|hint| {
        (
            format!("{:?}", hint.sink_fn),
            hint.contract_id,
            hint.param_idx,
        )
    });
    direct_hints.dedup_by(|lhs, rhs| {
        lhs.sink_fn == rhs.sink_fn
            && lhs.contract_id == rhs.contract_id
            && lhs.param_idx == rhs.param_idx
    });

    hazard_targets.sort_by_key(|target| {
        (
            format!("{:?}", target.sink_fn),
            format!("{:?}", target.post_fn),
            target.contract_id,
            target.place.pretty(),
            target.sp.to_string(),
        )
    });
    hazard_targets.dedup_by(|lhs, rhs| {
        lhs.sink_fn == rhs.sink_fn
            && lhs.post_fn == rhs.post_fn
            && lhs.contract_id == rhs.contract_id
            && lhs.place == rhs.place
            && lhs.sp == rhs.sp
    });

    (pairs, direct_hints, hazard_targets)
}

fn build_hazard_temporal_plans(
    tcx: TyCtxt<'_>,
    hazard_targets: &[HazardTarget],
) -> Vec<HazardTemporalPlan> {
    let mut plans = hazard_targets
        .iter()
        .map(|target| {
            HazardTemporalPlan::new(
                target.contract_id,
                tcx.def_path_str(target.sink_fn),
                tcx.def_path_str(target.post_fn),
            )
        })
        .collect_vec();
    plans.sort_by(|lhs, rhs| {
        (
            lhs.contract_id,
            lhs.source_fn.as_str(),
            lhs.invalidator_fn.as_str(),
        )
            .cmp(&(
                rhs.contract_id,
                rhs.source_fn.as_str(),
                rhs.invalidator_fn.as_str(),
            ))
    });
    plans.dedup();
    plans
}

fn effect_may_violate_contract(effect: &ContractEffect, instance: &ContractInstance) -> bool {
    match &effect.kind {
        EffectKind::WriteField { field, .. } => {
            instance_mentions_place(instance, field) && write_field_can_violate(&instance.sp)
        }
        EffectKind::InvalidateUtf8 { place } => {
            instance_mentions_place(instance, place)
                && matches!(
                    instance.sp,
                    PrimitiveSpKind::ValidString | PrimitiveSpKind::ValidCStr
                )
        }
        EffectKind::FreeAllocation { place } | EffectKind::DropSource { place } => {
            instance_mentions_place(instance, place)
                && matches!(
                    instance.sp,
                    PrimitiveSpKind::Allocated
                        | PrimitiveSpKind::ValidPtr
                        | PrimitiveSpKind::ValidPtr2Ref
                        | PrimitiveSpKind::InBound
                        | PrimitiveSpKind::Alive
                        | PrimitiveSpKind::Init
                )
        }
        EffectKind::CreateAlias { lhs, rhs } => {
            (instance_mentions_place(instance, lhs) || instance_mentions_place(instance, rhs))
                && matches!(
                    instance.sp,
                    PrimitiveSpKind::Alias
                        | PrimitiveSpKind::NotOwned
                        | PrimitiveSpKind::Alive
                        | PrimitiveSpKind::ValidPtr2Ref
                )
        }
        EffectKind::SetLen { place, .. } => {
            instance_mentions_place(instance, place)
                && matches!(
                    instance.sp,
                    PrimitiveSpKind::InBound
                        | PrimitiveSpKind::ValidNum
                        | PrimitiveSpKind::Allocated
                        | PrimitiveSpKind::ValidPtr
                        | PrimitiveSpKind::Init
                        | PrimitiveSpKind::ValidString
                )
        }
        EffectKind::AssumeInit { place } => {
            instance_mentions_place(instance, place)
                && matches!(instance.sp, PrimitiveSpKind::Init | PrimitiveSpKind::Typed)
        }
        EffectKind::ConstructAdt { .. } => {
            instance.adt_def.is_some()
                && matches!(
                    instance.sp,
                    PrimitiveSpKind::Align
                        | PrimitiveSpKind::DoubleAlign
                        | PrimitiveSpKind::Layout
                        | PrimitiveSpKind::ValidPtr
                        | PrimitiveSpKind::ValidPtr2Ref
                        | PrimitiveSpKind::ValidSlice
                        | PrimitiveSpKind::Init
                        | PrimitiveSpKind::InBound
                        | PrimitiveSpKind::ValidNum
                )
        }
    }
}

fn write_field_can_violate(sp: &PrimitiveSpKind) -> bool {
    matches!(
        sp,
        PrimitiveSpKind::Align
            | PrimitiveSpKind::DoubleAlign
            | PrimitiveSpKind::NonNull
            | PrimitiveSpKind::Null
            | PrimitiveSpKind::Allocated
            | PrimitiveSpKind::InBound
            | PrimitiveSpKind::NonOverlap
            | PrimitiveSpKind::ValidNum
            | PrimitiveSpKind::ValidString
            | PrimitiveSpKind::ValidCStr
            | PrimitiveSpKind::Init
            | PrimitiveSpKind::Unwrap
            | PrimitiveSpKind::Typed
            | PrimitiveSpKind::NotOwned
            | PrimitiveSpKind::Alias
            | PrimitiveSpKind::Alive
            | PrimitiveSpKind::Pinned
            | PrimitiveSpKind::ValidPtr
            | PrimitiveSpKind::ValidPtr2Ref
            | PrimitiveSpKind::Layout
            | PrimitiveSpKind::ValidSlice
            | PrimitiveSpKind::ValidTraitObj
    )
}

fn instance_mentions_place(instance: &ContractInstance, place: &SymbolicPlace) -> bool {
    instance
        .symbolic_args
        .iter()
        .any(|arg| place.is_prefix_of(arg) || arg.is_prefix_of(place))
}

fn const_may_violate_instance(instance: &ContractInstance, value: i128) -> bool {
    if let Some(kind) = instance.numeric_kind {
        return const_may_violate_numeric(kind, value);
    }

    match instance.sp {
        PrimitiveSpKind::InBound => value < 0 || value > 1024,
        PrimitiveSpKind::ValidNum => value == 0 || value > 1024,
        PrimitiveSpKind::ValidString => (0xD800..=0xDFFF).contains(&value) || value > 0x10FFFF,
        PrimitiveSpKind::NonNull | PrimitiveSpKind::ValidPtr => value == 0,
        PrimitiveSpKind::Align | PrimitiveSpKind::DoubleAlign => {
            value <= 0 || (value & (value - 1)) != 0
        }
        _ => true,
    }
}

fn resolve_arg_symbolic<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
    idx: usize,
    resolver: &PlaceResolver,
) -> Option<SymbolicPlace> {
    args.get(idx)
        .and_then(|arg| resolver.resolve_operand(tcx, fn_did, &arg.node))
}

fn collect_alias_from_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    resolver: &mut PlaceResolver,
    stmt: &StatementKind<'tcx>,
) {
    let StatementKind::Assign(assign) = stmt else {
        return;
    };
    let (lhs, rvalue) = &**assign;
    let rhs = match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => resolver.resolve_place(tcx, fn_did, place),
        Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
            resolver.resolve_place(tcx, fn_did, place)
        }
        _ => None,
    };
    if let Some(rhs) = rhs {
        resolver.record_alias(lhs, rhs);
    }
}

fn symbolic_places_from_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    rvalue: &Rvalue<'tcx>,
    resolver: &PlaceResolver,
) -> Vec<SymbolicPlace> {
    let mut places = Vec::new();
    let mut push_operand = |operand: &Operand<'tcx>| {
        if let Some(place) = resolver.resolve_operand(tcx, fn_did, operand) {
            places.push(place);
        }
    };

    match rvalue {
        Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => push_operand(operand),
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) | Rvalue::CopyForDeref(place) => {
            if let Some(place) = resolver.resolve_place(tcx, fn_did, place) {
                places.push(place);
            }
        }
        Rvalue::BinaryOp(_, operands) => {
            let (lhs, rhs) = &**operands;
            push_operand(lhs);
            push_operand(rhs);
        }
        Rvalue::Aggregate(_, operands) => {
            for operand in operands.iter() {
                push_operand(operand);
            }
        }
        _ => {}
    }

    places.sort_by_key(SymbolicPlace::pretty);
    places.dedup();
    places
}

fn raw_symbolic_place(tcx: TyCtxt<'_>, fn_did: DefId, place: &Place<'_>) -> Option<SymbolicPlace> {
    let local_idx = place.local.as_usize();
    let root = place_root_for_local(tcx, fn_did, local_idx);

    let mut fields = Vec::new();
    for proj in place.projection.iter() {
        match proj {
            ProjectionElem::Deref => {}
            ProjectionElem::Field(field, _) => fields.push(field.index()),
            _ => return None,
        }
    }
    Some(SymbolicPlace { root, fields })
}

fn place_root_for_local(tcx: TyCtxt<'_>, fn_did: DefId, local_idx: usize) -> PlaceRoot {
    let has_self = tcx
        .opt_associated_item(fn_did)
        .map(|item| matches!(item.kind, ty::AssocKind::Fn { has_self: true, .. }))
        .unwrap_or(false);

    if local_idx == 0 {
        PlaceRoot::Return
    } else if has_self && local_idx == 1 {
        PlaceRoot::Receiver
    } else if local_idx > 0
        && local_idx
            <= tcx
                .fn_sig(fn_did)
                .skip_binder()
                .inputs()
                .skip_binder()
                .len()
    {
        PlaceRoot::Param(local_idx - 1)
    } else {
        PlaceRoot::Local(local_idx)
    }
}

fn effect_value_from_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    rvalue: &Rvalue<'tcx>,
    resolver: &PlaceResolver,
) -> EffectValue {
    match rvalue {
        Rvalue::Use(operand) => effect_value_from_operand(tcx, fn_did, operand, resolver),
        Rvalue::Cast(_, operand, _) => effect_value_from_operand(tcx, fn_did, operand, resolver),
        Rvalue::BinaryOp(_, operands) => {
            let (lhs, rhs) = &**operands;
            match (
                effect_value_from_operand(tcx, fn_did, lhs, resolver),
                effect_value_from_operand(tcx, fn_did, rhs, resolver),
            ) {
                (EffectValue::Param(param), _) | (_, EffectValue::Param(param)) => {
                    EffectValue::Param(param)
                }
                (EffectValue::Const(_), EffectValue::Const(_)) => EffectValue::Unknown,
                _ => EffectValue::Unknown,
            }
        }
        _ => EffectValue::Unknown,
    }
}

fn effect_value_from_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    operand: &Operand<'tcx>,
    resolver: &PlaceResolver,
) -> EffectValue {
    if let Some(value) = const_operand_value(operand) {
        return EffectValue::Const(value);
    }
    let Some(place) = resolver.resolve_operand(tcx, fn_did, operand) else {
        return EffectValue::Unknown;
    };
    if let Some(param_idx) = place.is_param() {
        EffectValue::Param(param_idx)
    } else {
        EffectValue::Unknown
    }
}

fn const_operand_value(operand: &Operand<'_>) -> Option<i128> {
    let Operand::Constant(constant) = operand else {
        return None;
    };
    match constant.const_ {
        Const::Val(const_value, _) => const_value
            .try_to_scalar_int()
            .map(|scalar| scalar.to_uint(scalar.size()) as i128),
        _ => None,
    }
}

fn const_may_violate_numeric(kind: NumericPreconditionKind, value: i128) -> bool {
    match kind {
        NumericPreconditionKind::LessThanLen => value > 1024,
        NumericPreconditionKind::NonZero => value == 0,
        NumericPreconditionKind::PowerOfTwo => value <= 0 || (value & (value - 1)) != 0,
        NumericPreconditionKind::UnicodeScalar => {
            (0xD800..=0xDFFF).contains(&value) || value > 0x10FFFF
        }
        NumericPreconditionKind::OffsetInAllocation => value < 0 || value > 1024,
        NumericPreconditionKind::Expression => value == 0 || value > 1024,
    }
}

fn numeric_hints_for_expression_predicate(raw: &str) -> Option<Vec<NumericHint>> {
    let env = TypeSizeEnv::default().with_size("T", 16);
    let (_, hint) = direct_numeric_hint_for_predicate(raw, &env)?;
    match hint.kind {
        crate::analysis::testgen::context::InputHintKind::Numeric(hints) => Some(hints),
        _ => None,
    }
}

fn operand_fn_def(operand: &Operand<'_>) -> Option<DefId> {
    let Operand::Constant(func_constant) = operand else {
        return None;
    };
    let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() else {
        return None;
    };
    Some(*callee_def_id)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn predicate_binding_deserializes_compound_valid_num() {
        let binding: StdContractBinding = serde_json::from_str(
            r#"{
                "kind": "predicate",
                "predicate": "ValidNum(arg1 * size_of(T) <= isize::MAX)",
                "role": "slice_total_size"
            }"#,
        )
        .expect("predicate binding should deserialize");

        assert!(binding.matches_sp(&PrimitiveSpKind::ValidNum));
        assert_eq!(binding.role(), Some("slice_total_size"));
        assert_eq!(
            binding.numeric_kind(),
            Some(NumericPreconditionKind::Expression)
        );
        assert_eq!(binding.arg_indices(), vec![1]);
    }

    #[test]
    fn predicate_binding_deserializes_typed_inbound() {
        let binding: StdContractBinding = serde_json::from_str(
            r#"{
                "kind": "predicate",
                "predicate": "InBound(arg0, arg1, T)",
                "role": "ptr_len_object"
            }"#,
        )
        .expect("predicate binding should deserialize");

        assert!(binding.matches_sp(&PrimitiveSpKind::InBound));
        assert_eq!(binding.role(), Some("ptr_len_object"));
        assert_eq!(binding.arg_indices(), vec![0, 1]);
    }

    #[test]
    fn binding_deserializes_usage() {
        let binding: StdContractBinding = serde_json::from_str(
            r#"{
                "kind": "arg",
                "sp": "Alias",
                "arg": 0,
                "usage": "hazard",
                "role": "post_ref_alias"
            }"#,
        )
        .expect("binding usage should deserialize");

        assert!(binding.matches_sp(&PrimitiveSpKind::Alias));
        assert_eq!(binding.usage(), ContractUsage::Hazard);
        assert_eq!(binding.role(), Some("post_ref_alias"));
    }

    #[test]
    fn bundled_std_bindings_include_from_raw_parts_range_predicates() {
        let bindings = load_std_contract_bindings();
        let from_raw_parts = bindings
            .get("core::slice::raw::from_raw_parts")
            .expect("from_raw_parts binding should be bundled");

        assert!(from_raw_parts.iter().any(|binding| matches!(
            binding,
            StdContractBinding::Predicate { predicate, .. }
                if predicate.raw() == "InBound(arg0, arg1, T)"
        )));
        assert!(from_raw_parts.iter().any(|binding| matches!(
            binding,
            StdContractBinding::Predicate { predicate, .. }
                if predicate.raw() == "ValidNum(arg1 * size_of(T) <= isize::MAX)"
        )));
    }

    #[test]
    fn bundled_std_bindings_include_hazard_and_option_usage() {
        let bindings = load_std_contract_bindings();
        let as_ref = bindings
            .get("core::ptr::mut_ptr::as_ref")
            .expect("mut_ptr::as_ref binding should be bundled");
        assert!(as_ref.iter().any(|binding| {
            binding.matches_sp(&PrimitiveSpKind::Alias) && binding.usage() == ContractUsage::Hazard
        }));

        let as_mut_vec = bindings
            .get("alloc::string::as_mut_vec")
            .expect("String::as_mut_vec binding should be bundled");
        assert!(as_mut_vec.iter().any(|binding| {
            binding.matches_sp(&PrimitiveSpKind::ValidString)
                && binding.usage() == ContractUsage::Hazard
        }));

        let ptr_read = bindings
            .get("core::ptr::read")
            .expect("ptr::read binding should be bundled");
        assert!(ptr_read.iter().any(|binding| {
            binding.matches_sp(&PrimitiveSpKind::TraitCopy)
                && binding.usage() == ContractUsage::Option
        }));
    }

    #[test]
    fn json_hazard_bindings_are_lifted_even_when_std_db_has_preconditions() {
        let bindings = load_std_contract_bindings();
        let as_ref = bindings
            .get("core::ptr::mut_ptr::as_ref")
            .expect("mut_ptr::as_ref binding should be bundled");
        let lifted = binding_contract_specs(as_ref)
            .into_iter()
            .filter(|spec| should_lift_binding_contract_spec(true, spec))
            .collect_vec();

        assert!(
            lifted.iter().any(|spec| {
                spec.sp == PrimitiveSpKind::Alias && spec.usage == ContractUsage::Hazard
            }),
            "JSON-only Alias hazard should survive when the std contract DB supplies preconditions"
        );
        assert!(
            lifted
                .iter()
                .all(|spec| !matches!(spec.usage, ContractUsage::Precondition)),
            "precondition specs from JSON should not duplicate std contract DB properties"
        );
    }

    #[test]
    fn alias_hazard_matches_post_write_to_same_symbolic_place() {
        let dummy = rustc_hir::def_id::LOCAL_CRATE.as_def_id();
        let ptr_field = SymbolicPlace {
            root: PlaceRoot::Receiver,
            fields: vec![0],
        };
        let instance = ContractInstance {
            sink_fn: dummy,
            adt_def: Some(dummy),
            sink_self_ty: Some("&Cell".to_owned()),
            sink_signature: "fn(&Cell) -> &i32".to_owned(),
            sink_requires_monomorphization: false,
            std_fn: dummy,
            std_fn_name: "core::ptr::mut_ptr::as_ref".to_owned(),
            sp: PrimitiveSpKind::Alias,
            raw_tag: "Alias".to_owned(),
            symbolic_args: vec![ptr_field.clone()],
            usage: ContractUsage::Hazard,
            numeric_kind: None,
            binding_role: Some("post_ref_alias".to_owned()),
        };
        let effect = ContractEffect {
            fn_did: dummy,
            adt_def: Some(dummy),
            kind: EffectKind::WriteField {
                field: ptr_field,
                value: EffectValue::Param(1),
                inputs: Vec::new(),
            },
            confidence: EffectConfidence::Exact,
        };

        assert!(effect_may_violate_contract(&effect, &instance));
    }

    #[test]
    fn valid_num_expression_generates_negated_boundary_hints() {
        assert_eq!(
            numeric_hints_for_expression_predicate("ValidNum(arg1 != 0)"),
            Some(vec![NumericHint::Zero])
        );
        assert_eq!(
            numeric_hints_for_expression_predicate("ValidNum(arg1 <= 3)"),
            Some(vec![NumericHint::Literal(4)])
        );
        assert_eq!(
            numeric_hints_for_expression_predicate("ValidNum(arg1 < 3)"),
            Some(vec![NumericHint::Three, NumericHint::Literal(4)])
        );
        assert_eq!(
            numeric_hints_for_expression_predicate("ValidNum(arg1 * size_of(T) <= isize::MAX)"),
            Some(vec![NumericHint::Literal((isize::MAX as i128) / 16 + 1)])
        );
    }
}
