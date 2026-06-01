use crate::analysis::testgen::context::{Context, StmtKind};
use crate::analysis::testgen::contract::PrimitiveSpKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

pub const TESTGEN_ARTIFACT_SCHEMA_VERSION: usize = 2;

#[derive(Clone, Debug, Default, Serialize)]
pub struct ArtifactSummary {
    pub node_count: usize,
    pub edge_count: usize,
    pub action_count: usize,
    pub state_field_count: usize,
    pub contract_edge_count: usize,
    pub mutation_edge_count: usize,
    pub contract_count: usize,
    pub mutator_count: usize,
    pub recipe_count: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct ContractInstanceRecord {
    pub schema_version: usize,
    pub id: usize,
    pub stable_id: String,
    pub contract_edge_id: String,
    pub sink_fn: String,
    pub sink_def_id: String,
    pub sink_self_ty: Option<String>,
    pub sink_signature: String,
    pub sink_requires_monomorphization: bool,
    pub std_fn: String,
    pub std_fn_def_id: String,
    pub adt_def: Option<String>,
    pub sp: String,
    pub family: String,
    pub raw_tag: String,
    pub symbolic_args: Vec<String>,
    pub usage: String,
    pub numeric_template: Option<String>,
    pub binding_role: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ContractInstancesFile {
    pub schema_version: usize,
    pub db_loaded: bool,
    pub total: usize,
    pub instances: Vec<ContractInstanceRecord>,
}

impl ContractInstancesFile {
    pub fn write_json(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let file = File::create(path)?;
        serde_json::to_writer_pretty(file, self)?;
        Ok(())
    }
}

struct DotNodeStyle {
    shape: &'static str,
    fill: &'static str,
    color: &'static str,
}

impl DotNodeStyle {
    fn for_kind(kind: &str) -> Self {
        match kind {
            "action" => Self {
                shape: "box",
                fill: "#E8F1FF",
                color: "#2F5F9F",
            },
            "state_field" => Self {
                shape: "ellipse",
                fill: "#EAF7EA",
                color: "#3F7F3F",
            },
            "api" => Self {
                shape: "box",
                fill: "#E8F1FF",
                color: "#2F5F9F",
            },
            "std_api" => Self {
                shape: "box",
                fill: "#F3F3F3",
                color: "#666666",
            },
            "contract" => Self {
                shape: "diamond",
                fill: "#FFF2CC",
                color: "#A66A00",
            },
            "symbolic_place" => Self {
                shape: "ellipse",
                fill: "#EAF7EA",
                color: "#3F7F3F",
            },
            "mutator" => Self {
                shape: "box",
                fill: "#FCE4EC",
                color: "#A33A5B",
            },
            "recipe" => Self {
                shape: "note",
                fill: "#EFE7FF",
                color: "#6A4AA1",
            },
            "type" => Self {
                shape: "component",
                fill: "#E0F7FA",
                color: "#227C8A",
            },
            _ => Self {
                shape: "box",
                fill: "#FFFFFF",
                color: "#777777",
            },
        }
    }
}

struct DotEdgeStyle {
    color: &'static str,
}

impl DotEdgeStyle {
    fn for_kind(kind: &str) -> Self {
        let color = match kind {
            "mutates" => "#A33A5B",
            "uses" => "#2F5F9F",
            "contains" => "#3F7F3F",
            "contract" => "#D12B2B",
            "reaches" => "#2F5F9F",
            "calls_std" => "#666666",
            "binds" => "#3F7F3F",
            "api_mutator" | "exposes" => "#A33A5B",
            "writes" => "#7A4B00",
            "may_violate" => "#D12B2B",
            "realizes" | "direct_input" => "#6A4AA1",
            _ => "#777777",
        };
        Self { color }
    }
}

fn dot_node_label(node: &CcagNodeRecord) -> String {
    let label = compact_dot_label(&node.label, 42);
    match (
        node.kind.as_str(),
        node.attrs.get("action_kind").map(String::as_str),
    ) {
        ("action", Some("public_field_assignment")) => format!("write {label}"),
        ("action", Some("resource_recipe")) => format!("recipe {label}"),
        _ => label,
    }
}

fn dot_edge_label(edge: &CcagEdgeRecord) -> String {
    match edge.kind.as_str() {
        "uses" => edge
            .attrs
            .get("role")
            .filter(|role| !role.is_empty())
            .map(|role| format!("uses {role}"))
            .unwrap_or_else(|| "uses".to_owned()),
        "contract" => compact_dot_label(&edge.label, 28),
        "mutates" => match edge.label.as_str() {
            "WriteField" => "writes".to_owned(),
            "PublicFieldWrite" => "public write".to_owned(),
            "ConstructAdt" => "constructs".to_owned(),
            "recipe" => "recipe".to_owned(),
            other => compact_dot_label(other, 28),
        },
        "contains" => "contains".to_owned(),
        other => compact_dot_label(other, 28),
    }
}

fn compact_dot_label(raw: &str, max_chars: usize) -> String {
    let normalized = raw.split_whitespace().collect::<Vec<_>>().join(" ");
    if normalized.chars().count() <= max_chars {
        return normalized;
    }

    let mut truncated = normalized
        .chars()
        .take(max_chars.saturating_sub(3))
        .collect::<String>();
    truncated.push_str("...");
    truncated
}

fn dot_escape(raw: &str) -> String {
    raw.chars()
        .flat_map(|ch| match ch {
            '\\' => "\\\\".chars().collect::<Vec<_>>(),
            '"' => "\\\"".chars().collect(),
            '\n' => "\\n".chars().collect(),
            '\r' => Vec::new(),
            _ => vec![ch],
        })
        .collect()
}

#[derive(Clone, Debug, Serialize)]
pub struct CcagNodeRecord {
    pub id: String,
    pub kind: String,
    pub label: String,
    pub attrs: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct CcagEdgeRecord {
    pub source: String,
    pub target: String,
    pub kind: String,
    pub label: String,
    pub attrs: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct CcagFile {
    pub schema_version: usize,
    pub graph_kind: String,
    pub summary: ArtifactSummary,
    pub nodes: Vec<CcagNodeRecord>,
    pub edges: Vec<CcagEdgeRecord>,
}

impl CcagFile {
    pub fn empty() -> Self {
        Self {
            schema_version: TESTGEN_ARTIFACT_SCHEMA_VERSION,
            graph_kind: "contract_guided_api_graph".to_owned(),
            summary: ArtifactSummary::default(),
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }

    pub fn from_parts(nodes: Vec<CcagNodeRecord>, edges: Vec<CcagEdgeRecord>) -> Self {
        let mut seen_edges = BTreeSet::new();
        let edges = edges
            .into_iter()
            .filter(|edge| {
                let key = format!(
                    "{}\u{1f}{}\u{1f}{}\u{1f}{}\u{1f}{:?}",
                    edge.source, edge.target, edge.kind, edge.label, edge.attrs
                );
                seen_edges.insert(key)
            })
            .collect();
        let mut file = Self {
            schema_version: TESTGEN_ARTIFACT_SCHEMA_VERSION,
            graph_kind: "contract_guided_api_graph".to_owned(),
            summary: ArtifactSummary::default(),
            nodes,
            edges,
        };
        file.refresh_summary();
        file
    }

    fn refresh_summary(&mut self) {
        self.summary.node_count = self.nodes.len();
        self.summary.edge_count = self.edges.len();
        self.summary.action_count = self
            .nodes
            .iter()
            .filter(|node| node.kind == "action")
            .count();
        self.summary.state_field_count = self
            .nodes
            .iter()
            .filter(|node| node.kind == "state_field")
            .count();
        self.summary.contract_edge_count = self
            .edges
            .iter()
            .filter(|edge| edge.kind == "contract")
            .count();
        self.summary.mutation_edge_count = self
            .edges
            .iter()
            .filter(|edge| edge.kind == "mutates")
            .count();
        self.summary.contract_count = self
            .nodes
            .iter()
            .filter(|node| node.kind == "contract")
            .count();
        self.summary.mutator_count = self
            .nodes
            .iter()
            .filter(|node| node.kind == "mutator")
            .count();
        self.summary.recipe_count = self
            .nodes
            .iter()
            .filter(|node| node.kind == "recipe")
            .count();
    }

    pub fn write_json(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let file = File::create(path)?;
        serde_json::to_writer_pretty(file, self)?;
        Ok(())
    }

    pub fn write_dot(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let mut file = File::create(path)?;
        writeln!(file, "digraph CGAG {{")?;
        writeln!(file, "  rankdir=LR;")?;
        writeln!(
            file,
            "  graph [fontname=\"Helvetica\", fontsize=16, labelloc=t, label=\"Contract-Guided API Graph\"];"
        )?;
        writeln!(
            file,
            "  node [fontname=\"Helvetica\", fontsize=11, style=\"filled,rounded\", penwidth=1.4];"
        )?;
        writeln!(
            file,
            "  edge [fontname=\"Helvetica\", fontsize=10, arrowsize=0.75, penwidth=1.3];"
        )?;

        let node_aliases = self
            .nodes
            .iter()
            .enumerate()
            .map(|(idx, node)| (node.id.clone(), format!("n{idx}")))
            .collect::<BTreeMap<_, _>>();

        for node in &self.nodes {
            let style = DotNodeStyle::for_kind(&node.kind);
            writeln!(
                file,
                "  \"{}\" [label=\"{}\", shape=\"{}\", fillcolor=\"{}\", color=\"{}\"]",
                dot_escape(node_aliases.get(&node.id).map_or(&node.id, |alias| alias)),
                dot_escape(&dot_node_label(node)),
                style.shape,
                style.fill,
                style.color
            )?;
        }

        let mut rendered_edges = BTreeSet::new();
        for edge in &self.edges {
            let label = dot_edge_label(edge);
            let key = format!(
                "{}\u{1f}{}\u{1f}{}\u{1f}{}",
                edge.source, edge.target, edge.kind, label
            );
            if !rendered_edges.insert(key) {
                continue;
            }
            let style = DotEdgeStyle::for_kind(&edge.kind);
            writeln!(
                file,
                "  \"{}\" -> \"{}\" [label=\"{}\", color=\"{}\", fontcolor=\"{}\"]",
                dot_escape(
                    node_aliases
                        .get(&edge.source)
                        .map_or(&edge.source, |alias| alias)
                ),
                dot_escape(
                    node_aliases
                        .get(&edge.target)
                        .map_or(&edge.target, |alias| alias)
                ),
                dot_escape(&label),
                style.color,
                style.color
            )?;
        }

        writeln!(file, "}}")?;
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct CaseTargetRecord {
    pub contract_id: usize,
    pub contract_stable_id: String,
    pub contract_edge_id: String,
    pub target_kind: String,
    pub producer_fn: Option<String>,
    pub sink_fn: String,
    pub std_fn: String,
    pub sp: String,
    pub family: String,
    pub effect_kind: Option<String>,
    pub effect_confidence: Option<String>,
    pub hint_param: Option<usize>,
    pub hint_kind: Option<String>,
    pub reason: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct CaseHintRecord {
    pub var: String,
    pub ty: String,
    pub hint_kind: String,
    pub reason: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct CaseMetadata {
    pub schema_version: usize,
    pub case_name: String,
    pub case_path: String,
    pub calls: Vec<String>,
    pub sink_markers: Vec<usize>,
    pub executed_contracts: Vec<usize>,
    pub targets: Vec<CaseTargetRecord>,
    pub hints: Vec<CaseHintRecord>,
    pub compile_success: bool,
    pub miri_ub: bool,
    pub eval_result: String,
    pub eval_error: Option<String>,
}

impl CaseMetadata {
    pub fn empty(case_name: impl Into<String>, case_path: impl Into<PathBuf>) -> Self {
        Self {
            schema_version: TESTGEN_ARTIFACT_SCHEMA_VERSION,
            case_name: case_name.into(),
            case_path: case_path.into().display().to_string(),
            calls: Vec::new(),
            sink_markers: Vec::new(),
            executed_contracts: Vec::new(),
            targets: Vec::new(),
            hints: Vec::new(),
            compile_success: false,
            miri_ub: false,
            eval_result: "not_evaluated".to_owned(),
            eval_error: None,
        }
    }

    pub fn from_context<'tcx>(
        case_name: impl Into<String>,
        case_path: impl Into<PathBuf>,
        cx: &Context<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        let mut metadata = Self::empty(case_name, case_path);
        metadata.calls = cx
            .stmts()
            .iter()
            .filter_map(|stmt| match stmt.kind() {
                StmtKind::Call(call) => Some(
                    tcx.def_path_str_with_args(call.fn_did(), tcx.mk_args(call.generic_args())),
                ),
                _ => None,
            })
            .collect();

        metadata.sink_markers = cx
            .stmts()
            .iter()
            .filter_map(|stmt| match stmt.kind() {
                StmtKind::SinkMarker { contract_id, .. } => Some(*contract_id),
                _ => None,
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();

        metadata.hints = cx
            .stmts()
            .iter()
            .filter_map(|stmt| {
                let hint = cx.input_hint(stmt.place())?;
                Some(CaseHintRecord {
                    var: stmt.place().to_string(),
                    ty: cx.type_of(stmt.place()).to_string(),
                    hint_kind: format!("{:?}", hint.kind),
                    reason: hint.reason.clone(),
                })
            })
            .collect();

        metadata
    }

    pub fn set_eval_result(
        &mut self,
        eval_result: impl Into<String>,
        compile_success: bool,
        miri_ub: bool,
        executed_contracts: BTreeSet<usize>,
    ) {
        self.eval_result = eval_result.into();
        self.compile_success = compile_success;
        self.miri_ub = miri_ub;
        self.executed_contracts = executed_contracts.into_iter().collect();
        self.eval_error = None;
    }

    pub fn set_eval_error(&mut self, error: impl Into<String>) {
        self.eval_result = "evaluate_error".to_owned();
        self.compile_success = false;
        self.miri_ub = false;
        self.eval_error = Some(error.into());
    }

    pub fn write_json(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let file = File::create(path)?;
        serde_json::to_writer_pretty(file, self)?;
        Ok(())
    }
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct CoverageBucket {
    pub name: String,
    pub family: Option<String>,
    pub reached: usize,
    pub lifted: usize,
    pub bound: usize,
    pub violation_edge: usize,
    pub generated: usize,
    pub compiled: usize,
    pub sink_executed: usize,
    pub ub: usize,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct CoverageTotals {
    pub reached: usize,
    pub lifted: usize,
    pub bound: usize,
    pub violation_edge: usize,
    pub generated: usize,
    pub compiled: usize,
    pub sink_executed: usize,
    pub ub: usize,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct ContractCoverageReport {
    pub schema_version: usize,
    pub totals: CoverageTotals,
    pub per_sp: Vec<CoverageBucket>,
    pub per_family: Vec<CoverageBucket>,
}

#[derive(Clone, Debug, Default)]
pub struct ContractCoverage {
    instances: BTreeMap<usize, ContractInstanceRecord>,
    violation_edge: BTreeSet<usize>,
    generated: BTreeSet<usize>,
    compiled: BTreeSet<usize>,
    sink_executed: BTreeSet<usize>,
    ub: BTreeSet<usize>,
}

impl ContractCoverage {
    pub fn new(instances: Vec<ContractInstanceRecord>) -> Self {
        Self::new_with_static(instances, BTreeSet::new())
    }

    pub fn new_with_static(
        instances: Vec<ContractInstanceRecord>,
        violation_edge: BTreeSet<usize>,
    ) -> Self {
        Self {
            instances: instances
                .into_iter()
                .map(|instance| (instance.id, instance))
                .collect(),
            violation_edge,
            generated: BTreeSet::new(),
            compiled: BTreeSet::new(),
            sink_executed: BTreeSet::new(),
            ub: BTreeSet::new(),
        }
    }

    pub fn record_case(&mut self, metadata: &CaseMetadata) {
        let mut generated = BTreeSet::new();
        for target in &metadata.targets {
            if self.instances.contains_key(&target.contract_id) {
                generated.insert(target.contract_id);
            }
        }
        for contract_id in &metadata.sink_markers {
            if self.instances.contains_key(contract_id) {
                generated.insert(*contract_id);
            }
        }

        for contract_id in generated {
            self.generated.insert(contract_id);
            if metadata.compile_success {
                self.compiled.insert(contract_id);
            }
        }

        for contract_id in &metadata.executed_contracts {
            if self.instances.contains_key(contract_id) {
                self.sink_executed.insert(*contract_id);
                if metadata.miri_ub {
                    self.ub.insert(*contract_id);
                }
            }
        }
    }

    pub fn report(&self) -> ContractCoverageReport {
        let mut per_sp: BTreeMap<String, CoverageBucket> = BTreeMap::new();
        let mut per_family: BTreeMap<String, CoverageBucket> = BTreeMap::new();

        for (id, instance) in &self.instances {
            let sp_bucket = per_sp.entry(instance.sp.clone()).or_insert(CoverageBucket {
                name: instance.sp.clone(),
                family: Some(instance.family.clone()),
                reached: 0,
                lifted: 0,
                bound: 0,
                violation_edge: 0,
                generated: 0,
                compiled: 0,
                sink_executed: 0,
                ub: 0,
            });
            sp_bucket.reached += 1;
            sp_bucket.lifted += 1;
            if !instance.symbolic_args.is_empty() {
                sp_bucket.bound += 1;
            }
            if self.violation_edge.contains(id) {
                sp_bucket.violation_edge += 1;
            }
            if self.generated.contains(id) {
                sp_bucket.generated += 1;
            }
            if self.compiled.contains(id) {
                sp_bucket.compiled += 1;
            }
            if self.sink_executed.contains(id) {
                sp_bucket.sink_executed += 1;
            }
            if self.ub.contains(id) {
                sp_bucket.ub += 1;
            }

            let family_bucket =
                per_family
                    .entry(instance.family.clone())
                    .or_insert(CoverageBucket {
                        name: instance.family.clone(),
                        family: None,
                        reached: 0,
                        lifted: 0,
                        bound: 0,
                        violation_edge: 0,
                        generated: 0,
                        compiled: 0,
                        sink_executed: 0,
                        ub: 0,
                    });
            family_bucket.reached += 1;
            family_bucket.lifted += 1;
            if !instance.symbolic_args.is_empty() {
                family_bucket.bound += 1;
            }
            if self.violation_edge.contains(id) {
                family_bucket.violation_edge += 1;
            }
            if self.generated.contains(id) {
                family_bucket.generated += 1;
            }
            if self.compiled.contains(id) {
                family_bucket.compiled += 1;
            }
            if self.sink_executed.contains(id) {
                family_bucket.sink_executed += 1;
            }
            if self.ub.contains(id) {
                family_bucket.ub += 1;
            }
        }

        ContractCoverageReport {
            schema_version: TESTGEN_ARTIFACT_SCHEMA_VERSION,
            totals: CoverageTotals {
                reached: self.instances.len(),
                lifted: self.instances.len(),
                bound: self
                    .instances
                    .values()
                    .filter(|instance| !instance.symbolic_args.is_empty())
                    .count(),
                violation_edge: self.violation_edge.len(),
                generated: self.generated.len(),
                compiled: self.compiled.len(),
                sink_executed: self.sink_executed.len(),
                ub: self.ub.len(),
            },
            per_sp: per_sp.into_values().collect(),
            per_family: per_family.into_values().collect(),
        }
    }

    pub fn write_json(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let file = File::create(path)?;
        serde_json::to_writer_pretty(file, &self.report())?;
        Ok(())
    }
}

pub fn def_id_str(def_id: DefId) -> String {
    format!("{def_id:?}")
}

pub fn sp_name(sp: &PrimitiveSpKind) -> String {
    sp.to_string()
}

pub fn sp_family_name(sp: &PrimitiveSpKind) -> String {
    format!("{:?}", sp.family())
}
