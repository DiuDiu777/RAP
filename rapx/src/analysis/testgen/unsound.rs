use crate::analysis::testgen::context::{ApiCall, InputHint, Stmt, StmtKind, Var, DUMMY_INPUT_VAR};
use crate::analysis::testgen::context_builder::ContextBuilder;
use crate::analysis::testgen::contract::{PrimitiveSpKind, SafetyContractDb};
use crate::analysis::testgen::coverage::{
    def_id_str, sp_family_name, sp_name, CaseMetadata, CaseTargetRecord, CcagEdgeRecord, CcagFile,
    CcagNodeRecord, ContractInstanceRecord, ContractInstancesFile,
};
use crate::analysis::testgen::guide::{ContractTarget, FuzzGuide, GuidedAction};
use crate::analysis::testgen::utils::is_def_id_public;
use crate::analysis::utils::fn_info::{
    check_safety, get_adt_def_id_by_adt_method, get_cleaned_def_path_name,
};
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_hir::{BodyOwnerKind, LangItem};
use rustc_middle::mir::{
    Const, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs::File;
use std::io::{self, Write};
use std::path::Path;

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
enum PlaceRoot {
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

    fn pretty(&self) -> String {
        let root = match self.root {
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

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
#[allow(dead_code)]
enum ContractUsage {
    Precondition,
    Hazard,
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

#[derive(Debug, Clone, Copy)]
enum NumericPreconditionKind {
    LessThanLen,
    NonZero,
    PowerOfTwo,
    UnicodeScalar,
    OffsetInAllocation,
}

impl NumericPreconditionKind {
    fn invalid_hint(self, reason: impl Into<String>) -> InputHint {
        match self {
            Self::LessThanLen => InputHint::invalid_index(reason),
            Self::NonZero | Self::PowerOfTwo => InputHint::invalid_align(reason),
            Self::UnicodeScalar => InputHint::invalid_unicode_scalar(reason),
            Self::OffsetInAllocation => InputHint::negative_offset(reason),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::LessThanLen => "lt_len",
            Self::NonZero => "non_zero",
            Self::PowerOfTwo => "power_of_two",
            Self::UnicodeScalar => "unicode_scalar",
            Self::OffsetInAllocation => "offset_in_allocation",
        }
    }

    fn sp_kind(self) -> PrimitiveSpKind {
        match self {
            Self::LessThanLen | Self::OffsetInAllocation => PrimitiveSpKind::InBound,
            Self::NonZero | Self::PowerOfTwo => PrimitiveSpKind::ValidNum,
            Self::UnicodeScalar => PrimitiveSpKind::ValidString,
        }
    }
}

#[derive(Debug, Clone)]
struct ContractInstance {
    sink_fn: DefId,
    adt_def: Option<DefId>,
    std_fn: DefId,
    std_fn_name: String,
    sp: PrimitiveSpKind,
    raw_tag: String,
    symbolic_args: Vec<SymbolicPlace>,
    usage: ContractUsage,
    numeric_kind: Option<NumericPreconditionKind>,
}

impl ContractInstance {
    fn sensitive_place(&self) -> Option<&SymbolicPlace> {
        self.symbolic_args.first()
    }

    fn invalid_hint(&self, reason: impl Into<String>) -> Option<InputHint> {
        let reason = reason.into();
        if let Some(kind) = self.numeric_kind {
            return Some(kind.invalid_hint(reason));
        }

        match self.sp {
            PrimitiveSpKind::InBound => Some(InputHint::invalid_index(reason)),
            PrimitiveSpKind::Align | PrimitiveSpKind::DoubleAlign => {
                Some(InputHint::misaligned_ptr(reason))
            }
            PrimitiveSpKind::ValidNum => Some(InputHint::invalid_align(reason)),
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

    fn args_pretty(&self) -> String {
        self.symbolic_args
            .iter()
            .map(SymbolicPlace::pretty)
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
        }
    }

    fn value(&self) -> Option<EffectValue> {
        match self {
            Self::WriteField { value, .. } | Self::SetLen { value, .. } => Some(*value),
            _ => None,
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
        }
    }
}

#[derive(Debug, Clone)]
struct ContractEffect {
    fn_did: DefId,
    adt_def: Option<DefId>,
    kind: EffectKind,
}

#[derive(Debug, Clone)]
struct ConflictPair {
    contract_id: usize,
    producer_fn: DefId,
    sink_fn: DefId,
    place: SymbolicPlace,
    sp: PrimitiveSpKind,
    effect_kind: &'static str,
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
    field_index: usize,
    field_name: String,
    place: SymbolicPlace,
    sp: PrimitiveSpKind,
    hint: Option<InputHint>,
    reason: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum StdContractBinding {
    LtLen {
        value_arg: usize,
        container_arg: usize,
    },
    NonZero {
        arg: usize,
    },
    PowerOfTwo {
        arg: usize,
    },
    UnicodeScalar {
        arg: usize,
    },
    OffsetInAlloc {
        offset_arg: usize,
        ptr_arg: usize,
    },
    Arg {
        arg: usize,
        sp: Option<String>,
    },
}

impl StdContractBinding {
    fn numeric_kind(&self) -> Option<NumericPreconditionKind> {
        match self {
            Self::LtLen { .. } => Some(NumericPreconditionKind::LessThanLen),
            Self::NonZero { .. } => Some(NumericPreconditionKind::NonZero),
            Self::PowerOfTwo { .. } => Some(NumericPreconditionKind::PowerOfTwo),
            Self::UnicodeScalar { .. } => Some(NumericPreconditionKind::UnicodeScalar),
            Self::OffsetInAlloc { .. } => Some(NumericPreconditionKind::OffsetInAllocation),
            Self::Arg { .. } => None,
        }
    }

    fn matches_sp(&self, sp: &PrimitiveSpKind) -> bool {
        if let Some(kind) = self.numeric_kind() {
            return kind.sp_kind() == *sp;
        }

        match self {
            Self::Arg {
                sp: Some(raw_tag), ..
            } => PrimitiveSpKind::from_tag(raw_tag) == *sp,
            Self::Arg { sp: None, .. } => true,
            _ => false,
        }
    }
}

#[derive(Default)]
struct PlaceResolver {
    aliases: HashMap<usize, SymbolicPlace>,
}

impl PlaceResolver {
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

#[derive(Clone)]
pub struct ContractGuide<'tcx> {
    tcx: TyCtxt<'tcx>,
    instances: Vec<ContractInstance>,
    effects: Vec<ContractEffect>,
    pairs: Vec<ConflictPair>,
    direct_hints: Vec<DirectSinkHint>,
    public_field_targets: Vec<PublicFieldTarget>,
    contract_db_loaded: bool,
    _marker: std::marker::PhantomData<&'tcx ()>,
}

impl<'tcx> ContractGuide<'tcx> {
    pub fn analyze(tcx: TyCtxt<'tcx>) -> Self {
        let contract_db = match SafetyContractDb::load_default() {
            Ok(db) => {
                let instances = collect_lifted_preconditions(tcx, &db);
                let effects = collect_effects(tcx);
                let (pairs, direct_hints) = build_conflicts(&instances, &effects);
                let public_field_targets = collect_public_field_targets(tcx, &instances);
                return Self {
                    tcx,
                    instances,
                    effects,
                    pairs,
                    direct_hints,
                    public_field_targets,
                    contract_db_loaded: true,
                    _marker: std::marker::PhantomData,
                };
            }
            Err(_) => SafetyContractDb::default(),
        };

        let instances = collect_lifted_preconditions(tcx, &contract_db);
        let effects = collect_effects(tcx);
        let (pairs, direct_hints) = build_conflicts(&instances, &effects);
        let public_field_targets = collect_public_field_targets(tcx, &instances);
        Self {
            tcx,
            instances,
            effects,
            pairs,
            direct_hints,
            public_field_targets,
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
                id,
                sink_fn: tcx.def_path_str(instance.sink_fn),
                sink_def_id: def_id_str(instance.sink_fn),
                std_fn: instance.std_fn_name.clone(),
                std_fn_def_id: def_id_str(instance.std_fn),
                adt_def: instance.adt_def.map(|def_id| tcx.def_path_str(def_id)),
                sp: sp_name(&instance.sp),
                family: sp_family_name(&instance.sp),
                raw_tag: instance.raw_tag.clone(),
                symbolic_args: instance
                    .symbolic_args
                    .iter()
                    .map(SymbolicPlace::pretty)
                    .collect(),
                usage: instance.usage.name().to_owned(),
                numeric_template: instance.numeric_kind.map(|kind| kind.name().to_owned()),
            })
            .collect()
    }

    pub fn contract_instances_file(&self, tcx: TyCtxt<'tcx>) -> ContractInstancesFile {
        let instances = self.contract_instance_records(tcx);
        ContractInstancesFile {
            db_loaded: self.contract_db_loaded,
            total: instances.len(),
            instances,
        }
    }

    pub fn dump_instances_json(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> io::Result<()> {
        self.contract_instances_file(tcx).write_json(path)
    }

    pub fn ccag_file(&self, tcx: TyCtxt<'tcx>) -> CcagFile {
        let mut nodes = BTreeMap::new();
        let mut edges = Vec::new();

        for (contract_id, instance) in self.instances.iter().enumerate() {
            let sink_id = api_node_id(instance.sink_fn);
            insert_ccag_node(
                &mut nodes,
                sink_id.clone(),
                "api",
                tcx.def_path_str(instance.sink_fn),
                attrs(&[("def_id", def_id_str(instance.sink_fn))]),
            );

            let std_id = api_node_id(instance.std_fn);
            insert_ccag_node(
                &mut nodes,
                std_id.clone(),
                "std_api",
                instance.std_fn_name.clone(),
                attrs(&[("def_id", def_id_str(instance.std_fn))]),
            );

            let contract_id_str = contract_node_id(contract_id);
            insert_ccag_node(
                &mut nodes,
                contract_id_str.clone(),
                "contract",
                format!("{}:{}", sp_name(&instance.sp), contract_id),
                attrs(&[
                    ("sp", sp_name(&instance.sp)),
                    ("family", sp_family_name(&instance.sp)),
                    ("usage", instance.usage.name().to_owned()),
                    ("raw_tag", instance.raw_tag.clone()),
                    ("std_fn", instance.std_fn_name.clone()),
                ]),
            );

            edges.push(ccag_edge(
                sink_id,
                contract_id_str.clone(),
                "reaches",
                "reaches",
                BTreeMap::new(),
            ));
            edges.push(ccag_edge(
                contract_id_str.clone(),
                std_id,
                "calls_std",
                "calls",
                BTreeMap::new(),
            ));

            for (arg_idx, place) in instance.symbolic_args.iter().enumerate() {
                let place_id = place_node_id(place);
                insert_ccag_node(
                    &mut nodes,
                    place_id.clone(),
                    "symbolic_place",
                    place.pretty(),
                    BTreeMap::new(),
                );
                edges.push(ccag_edge(
                    contract_id_str.clone(),
                    place_id,
                    "binds",
                    format!("arg{arg_idx}"),
                    attrs(&[("role", format!("arg{arg_idx}"))]),
                ));
            }
        }

        for pair in &self.pairs {
            let producer_id = api_node_id(pair.producer_fn);
            insert_ccag_node(
                &mut nodes,
                producer_id.clone(),
                "api",
                tcx.def_path_str(pair.producer_fn),
                attrs(&[("def_id", def_id_str(pair.producer_fn))]),
            );

            let mutator_id = api_mutator_node_id(pair);
            insert_ccag_node(
                &mut nodes,
                mutator_id.clone(),
                "mutator",
                format!(
                    "{} mutates {}",
                    tcx.def_path_str(pair.producer_fn),
                    pair.place.pretty()
                ),
                attrs(&[
                    ("source", "api_call".to_owned()),
                    ("effect", pair.effect_kind.to_owned()),
                    ("contract_id", pair.contract_id.to_string()),
                    ("reason", pair.reason.clone()),
                ]),
            );
            edges.push(ccag_edge(
                producer_id,
                mutator_id.clone(),
                "api_mutator",
                "mutates",
                BTreeMap::new(),
            ));
            edges.push(ccag_edge(
                mutator_id.clone(),
                place_node_id(&pair.place),
                "writes",
                "writes",
                BTreeMap::new(),
            ));
            edges.push(ccag_edge(
                mutator_id.clone(),
                contract_node_id(pair.contract_id),
                "may_violate",
                "may violate",
                attrs(&[("sp", sp_name(&pair.sp))]),
            ));
            if let Some(hint) = &pair.hint {
                let recipe_id = recipe_node_id(pair.contract_id, &format!("{:?}", hint.kind));
                insert_ccag_node(
                    &mut nodes,
                    recipe_id.clone(),
                    "recipe",
                    format!("{:?}", hint.kind),
                    attrs(&[("reason", hint.reason.clone())]),
                );
                edges.push(ccag_edge(
                    recipe_id,
                    mutator_id,
                    "realizes",
                    "realizes",
                    BTreeMap::new(),
                ));
            }
        }

        for target in &self.public_field_targets {
            let type_id = type_node_id(target.adt_def);
            insert_ccag_node(
                &mut nodes,
                type_id.clone(),
                "type",
                tcx.def_path_str(target.adt_def),
                attrs(&[("def_id", def_id_str(target.adt_def))]),
            );

            let mutator_id = public_field_mutator_node_id(target);
            insert_ccag_node(
                &mut nodes,
                mutator_id.clone(),
                "mutator",
                format!("{}.{}", tcx.def_path_str(target.adt_def), target.field_name),
                attrs(&[
                    ("source", "public_field".to_owned()),
                    ("field", target.field_name.clone()),
                    ("effect", "PublicFieldWrite".to_owned()),
                    ("contract_id", target.contract_id.to_string()),
                    ("reason", target.reason.clone()),
                ]),
            );
            edges.push(ccag_edge(
                type_id,
                mutator_id.clone(),
                "exposes",
                "exposes",
                BTreeMap::new(),
            ));
            edges.push(ccag_edge(
                mutator_id.clone(),
                place_node_id(&target.place),
                "writes",
                "writes",
                BTreeMap::new(),
            ));
            edges.push(ccag_edge(
                mutator_id.clone(),
                contract_node_id(target.contract_id),
                "may_violate",
                "may violate",
                attrs(&[("sp", sp_name(&target.sp))]),
            ));
            if let Some(hint) = &target.hint {
                let recipe_id = recipe_node_id(target.contract_id, &format!("{:?}", hint.kind));
                insert_ccag_node(
                    &mut nodes,
                    recipe_id.clone(),
                    "recipe",
                    format!("{:?}", hint.kind),
                    attrs(&[("reason", hint.reason.clone())]),
                );
                edges.push(ccag_edge(
                    recipe_id,
                    mutator_id,
                    "realizes",
                    "realizes",
                    BTreeMap::new(),
                ));
            }
        }

        for direct in &self.direct_hints {
            let recipe_id = recipe_node_id(direct.contract_id, &format!("{:?}", direct.hint.kind));
            insert_ccag_node(
                &mut nodes,
                recipe_id.clone(),
                "recipe",
                format!("{:?}", direct.hint.kind),
                attrs(&[("reason", direct.reason.clone())]),
            );
            edges.push(ccag_edge(
                recipe_id,
                contract_node_id(direct.contract_id),
                "direct_input",
                format!("arg{}", direct.param_idx),
                attrs(&[("param", direct.param_idx.to_string())]),
            ));
        }

        CcagFile {
            version: 1,
            nodes: nodes.into_values().collect(),
            edges,
        }
    }

    pub fn dump_ccag_json(&self, path: impl AsRef<Path>, tcx: TyCtxt<'tcx>) -> io::Result<()> {
        self.ccag_file(tcx).write_json(path)
    }

    pub fn violation_edge_contract_ids(&self) -> BTreeSet<usize> {
        self.pairs
            .iter()
            .map(|pair| pair.contract_id)
            .chain(self.direct_hints.iter().map(|hint| hint.contract_id))
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
            let Some(sink_positions) = call_positions.get(&pair.sink_fn) else {
                continue;
            };
            if !producer_positions
                .iter()
                .any(|producer| sink_positions.iter().any(|sink| producer <= sink))
            {
                continue;
            }

            let Some(instance) = self.instances.get(pair.contract_id) else {
                continue;
            };
            targets.push(CaseTargetRecord {
                contract_id: pair.contract_id,
                target_kind: "producer_sink".to_owned(),
                producer_fn: Some(tcx.def_path_str(pair.producer_fn)),
                sink_fn: tcx.def_path_str(pair.sink_fn),
                std_fn: instance.std_fn_name.clone(),
                sp: sp_name(&instance.sp),
                family: sp_family_name(&instance.sp),
                effect_kind: Some(pair.effect_kind.to_owned()),
                hint_param: pair.hint_param,
                hint_kind: pair.hint.as_ref().map(|hint| format!("{:?}", hint.kind)),
                reason: pair.reason.clone(),
            });
        }

        for direct in &self.direct_hints {
            if !call_positions.contains_key(&direct.sink_fn) {
                continue;
            }
            let Some(instance) = self.instances.get(direct.contract_id) else {
                continue;
            };
            targets.push(CaseTargetRecord {
                contract_id: direct.contract_id,
                target_kind: "direct_sink".to_owned(),
                producer_fn: None,
                sink_fn: tcx.def_path_str(direct.sink_fn),
                std_fn: instance.std_fn_name.clone(),
                sp: sp_name(&instance.sp),
                family: sp_family_name(&instance.sp),
                effect_kind: None,
                hint_param: Some(direct.param_idx),
                hint_kind: Some(format!("{:?}", direct.hint.kind)),
                reason: direct.reason.clone(),
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
                    if call.fn_did() != public_field.sink_fn {
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
                target_kind: "public_field".to_owned(),
                producer_fn: None,
                sink_fn: tcx.def_path_str(public_field.sink_fn),
                std_fn: instance.std_fn_name.clone(),
                sp: sp_name(&instance.sp),
                family: sp_family_name(&instance.sp),
                effect_kind: Some("PublicFieldWrite".to_owned()),
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
                hints[param_idx] = pair.hint.clone();
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
            if hints.len() <= direct.param_idx {
                hints.resize(direct.param_idx + 1, None);
            }
            if hints[direct.param_idx].is_none() {
                hints[direct.param_idx] = Some(direct.hint.clone());
            }
        }
        hints
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

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
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
                    None => 80.0,
                };
            }
            if pair.sink_fn == fn_did {
                let receiver = action.call.args().first().copied();
                let ready = receiver
                    .map(|var| self.has_prior_producer_for_receiver(builder, pair, var))
                    .unwrap_or(false);
                score += if ready { 260.0 } else { 20.0 };
            }
        }

        for direct in &self.direct_hints {
            if direct.sink_fn == fn_did {
                score += if action.call.args().get(direct.param_idx) == Some(&DUMMY_INPUT_VAR) {
                    180.0
                } else {
                    20.0
                };
            }
        }

        for target in &self.public_field_targets {
            if target.sink_fn == fn_did {
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
            .filter(|(_, instance)| instance.sink_fn == call.fn_did())
        {
            builder.add_sink_marker_stmt(contract_id, self.tcx.def_path_str(instance.sink_fn));
        }
    }

    fn contract_targets(&self, builder: &ContextBuilder<'tcx, '_>) -> Vec<ContractTarget> {
        let mut priorities = BTreeMap::new();
        for (contract_id, instance) in self.instances.iter().enumerate() {
            let already_called = builder.cx().stmts().iter().any(|stmt| {
                matches!(stmt.kind(), StmtKind::Call(call) if call.fn_did() == instance.sink_fn)
            });
            if already_called {
                continue;
            }
            priorities.insert(contract_id, (instance.sink_fn, 10.0));
        }
        for direct in &self.direct_hints {
            priorities
                .entry(direct.contract_id)
                .and_modify(|(_, priority)| *priority += 180.0);
        }
        for pair in &self.pairs {
            priorities
                .entry(pair.contract_id)
                .and_modify(|(_, priority)| *priority += 120.0);
        }
        for target in &self.public_field_targets {
            priorities
                .entry(target.contract_id)
                .and_modify(|(_, priority)| *priority += 220.0);
        }

        priorities
            .into_iter()
            .map(|(contract_id, (sink_fn, priority))| ContractTarget {
                contract_id,
                sink_fn,
                priority,
            })
            .collect()
    }

    fn summary(&self, tcx: TyCtxt<'tcx>) -> String {
        let mut s = String::new();
        s.push_str(&format!(
            "contract: db_loaded={}, instances={}, effects={}, pairs={}, direct_hints={}, public_field_targets={}\n",
            self.contract_db_loaded,
            self.instances.len(),
            self.effects.len(),
            self.pairs.len(),
            self.direct_hints.len(),
            self.public_field_targets.len()
        ));

        if !self.instances.is_empty() {
            s.push_str("instances:\n");
            for instance in self.instances.iter().take(96) {
                s.push_str(&format!(
                    "  {} via {} ({:?}) requires {}({}) [{}]{} raw={}\n",
                    tcx.def_path_str(instance.sink_fn),
                    instance.std_fn_name,
                    instance.std_fn,
                    instance.sp,
                    instance.args_pretty(),
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
                    effect.kind.primary_place().pretty()
                ));
            }
        }

        if !self.pairs.is_empty() {
            s.push_str("pairs:\n");
            for pair in self.pairs.iter().take(96) {
                s.push_str(&format!(
                    "  {} -> {} on {} via {} violates {} ({})\n",
                    tcx.def_path_str(pair.producer_fn),
                    tcx.def_path_str(pair.sink_fn),
                    pair.place.pretty(),
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

fn api_node_id(def_id: DefId) -> String {
    format!("api:{def_id:?}")
}

fn type_node_id(def_id: DefId) -> String {
    format!("type:{def_id:?}")
}

fn contract_node_id(contract_id: usize) -> String {
    format!("contract:{contract_id}")
}

fn place_node_id(place: &SymbolicPlace) -> String {
    format!("place:{}", place.pretty())
}

fn api_mutator_node_id(pair: &ConflictPair) -> String {
    format!(
        "mutator:api:{:?}:{}:{}",
        pair.producer_fn,
        pair.contract_id,
        pair.place.pretty()
    )
}

fn public_field_mutator_node_id(target: &PublicFieldTarget) -> String {
    format!(
        "mutator:public-field:{:?}:{}:{}",
        target.adt_def, target.field_name, target.contract_id
    )
}

fn recipe_node_id(contract_id: usize, hint_kind: &str) -> String {
    format!("recipe:{contract_id}:{hint_kind}")
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

fn field_name_for_index(tcx: TyCtxt<'_>, adt_def: DefId, field_index: usize) -> Option<String> {
    let adt = tcx.adt_def(adt_def);
    if !adt.is_struct() {
        return None;
    }
    adt.non_enum_variant()
        .fields
        .iter()
        .nth(field_index)
        .map(|field| field.name.to_string())
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
    if !adt_def.is_struct() {
        return None;
    }
    adt_def
        .non_enum_variant()
        .fields
        .iter()
        .nth(target.field_index)
        .map(|field| field.ty(tcx, args))
}

fn collect_public_field_targets<'tcx>(
    tcx: TyCtxt<'tcx>,
    instances: &[ContractInstance],
) -> Vec<PublicFieldTarget> {
    let mut targets = Vec::new();

    for (contract_id, instance) in instances.iter().enumerate() {
        let Some(adt_def) = instance.adt_def else {
            continue;
        };
        for place in instance
            .sensitive_place()
            .into_iter()
            .filter(|place| place.is_receiver_field())
        {
            if place.fields.len() != 1 {
                continue;
            }
            let field_index = place.fields[0];
            if !is_public_field(tcx, adt_def, field_index) {
                continue;
            }
            let Some(field_name) = field_name_for_index(tcx, adt_def, field_index) else {
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
                field_index,
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
            target.field_index,
        )
    });
    targets.dedup_by(|lhs, rhs| {
        lhs.contract_id == rhs.contract_id
            && lhs.sink_fn == rhs.sink_fn
            && lhs.adt_def == rhs.adt_def
            && lhs.field_index == rhs.field_index
    });
    targets
}

fn load_std_contract_bindings() -> HashMap<String, Vec<StdContractBinding>> {
    serde_json::from_str(include_str!("data/std_contract_bindings.json"))
        .expect("Unable to parse std contract bindings")
}

fn collect_lifted_preconditions<'tcx>(
    tcx: TyCtxt<'tcx>,
    contract_db: &SafetyContractDb,
) -> Vec<ContractInstance> {
    let contract_bindings = load_std_contract_bindings();
    let mut instances = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        if !matches!(tcx.hir_body_owner_kind(local_def_id), BodyOwnerKind::Fn) {
            continue;
        }
        let fn_did = local_def_id.to_def_id();
        if !is_def_id_public(fn_did, tcx) || check_safety(tcx, fn_did) {
            continue;
        }
        let adt_def = get_adt_def_id_by_adt_method(tcx, fn_did);
        let body = tcx.optimized_mir(fn_did);
        let mut resolver = PlaceResolver::default();
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
            let callee_name = get_cleaned_def_path_name(tcx, callee_def_id);
            let Some(contract) = contract_db.get(&callee_name) else {
                continue;
            };
            let bindings = contract_bindings.get(&callee_name);
            for properties in contract.sites().values() {
                for property in properties {
                    instances.extend(lift_property_instances(
                        tcx,
                        fn_did,
                        adt_def,
                        callee_def_id,
                        &callee_name,
                        property.raw_tag(),
                        property.kind().clone(),
                        bindings.map(Vec::as_slice).unwrap_or(&[]),
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
            std_fn,
            std_fn_name: std_fn_name.to_owned(),
            sp: sp.clone(),
            raw_tag: raw_tag.to_owned(),
            symbolic_args,
            usage: ContractUsage::Precondition,
            numeric_kind: binding.numeric_kind(),
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
        std_fn,
        std_fn_name: std_fn_name.to_owned(),
        sp,
        raw_tag: raw_tag.to_owned(),
        symbolic_args,
        usage: ContractUsage::Precondition,
        numeric_kind: None,
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
    match binding {
        StdContractBinding::LtLen {
            value_arg,
            container_arg,
        } => Some(vec![resolve(*value_arg)?, resolve(*container_arg)?]),
        StdContractBinding::NonZero { arg }
        | StdContractBinding::PowerOfTwo { arg }
        | StdContractBinding::UnicodeScalar { arg }
        | StdContractBinding::Arg { arg, .. } => Some(vec![resolve(*arg)?]),
        StdContractBinding::OffsetInAlloc {
            offset_arg,
            ptr_arg,
        } => Some(vec![resolve(*offset_arg)?, resolve(*ptr_arg)?]),
    }
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

fn collect_effects<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<ContractEffect> {
    let mut effects = Vec::new();
    for local_def_id in tcx.hir_body_owners() {
        if !matches!(tcx.hir_body_owner_kind(local_def_id), BodyOwnerKind::Fn) {
            continue;
        }
        let fn_did = local_def_id.to_def_id();
        if !is_def_id_public(fn_did, tcx) || check_safety(tcx, fn_did) {
            continue;
        }
        let adt_def = get_adt_def_id_by_adt_method(tcx, fn_did);
        let body = tcx.optimized_mir(fn_did);
        let mut resolver = PlaceResolver::default();
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
    let Some(field) = raw_symbolic_place(tcx, fn_did, lhs) else {
        return;
    };
    if !field.is_receiver_field() {
        return;
    }
    let value = effect_value_from_rvalue(tcx, fn_did, rvalue, resolver);
    effects.push(ContractEffect {
        fn_did,
        adt_def,
        kind: EffectKind::WriteField { field, value },
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
        });
    } else if callee_name.ends_with("::as_mut_vec") || callee_name.ends_with("::as_bytes_mut") {
        effects.push(ContractEffect {
            fn_did,
            adt_def,
            kind: EffectKind::InvalidateUtf8 { place: first_place },
        });
    } else if callee_name.contains("::from_raw") || callee_name.contains("::dealloc") {
        effects.push(ContractEffect {
            fn_did,
            adt_def,
            kind: EffectKind::FreeAllocation { place: first_place },
        });
    } else if callee_name.contains("::assume_init") {
        effects.push(ContractEffect {
            fn_did,
            adt_def,
            kind: EffectKind::AssumeInit { place: first_place },
        });
    }
}

fn build_conflicts(
    instances: &[ContractInstance],
    effects: &[ContractEffect],
) -> (Vec<ConflictPair>, Vec<DirectSinkHint>) {
    let mut pairs = Vec::new();
    let mut direct_hints = Vec::new();

    for (contract_id, instance) in instances.iter().enumerate() {
        if let Some(param_idx) = instance.sensitive_place().and_then(SymbolicPlace::is_param) {
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
            let reason = format!(
                "{} on {} can break {} required by {}",
                effect.kind.name(),
                place.pretty(),
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

    (pairs, direct_hints)
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
    instance.symbolic_args.iter().any(|arg| arg == place)
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

fn raw_symbolic_place(tcx: TyCtxt<'_>, fn_did: DefId, place: &Place<'_>) -> Option<SymbolicPlace> {
    let local_idx = place.local.as_usize();
    let has_self = tcx
        .opt_associated_item(fn_did)
        .map(|item| matches!(item.kind, ty::AssocKind::Fn { has_self: true, .. }))
        .unwrap_or(false);

    let root = if has_self && local_idx == 1 {
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
    };

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
