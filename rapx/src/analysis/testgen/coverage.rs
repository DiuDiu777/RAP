use crate::analysis::testgen::context::{Context, StmtKind};
use crate::analysis::testgen::contract::PrimitiveSpKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, Serialize)]
pub struct ContractInstanceRecord {
    pub id: usize,
    pub sink_fn: String,
    pub sink_def_id: String,
    pub std_fn: String,
    pub std_fn_def_id: String,
    pub adt_def: Option<String>,
    pub sp: String,
    pub family: String,
    pub raw_tag: String,
    pub symbolic_args: Vec<String>,
    pub usage: String,
    pub numeric_template: Option<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ContractInstancesFile {
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
    pub version: usize,
    pub nodes: Vec<CcagNodeRecord>,
    pub edges: Vec<CcagEdgeRecord>,
}

impl CcagFile {
    pub fn empty() -> Self {
        Self {
            version: 1,
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }

    pub fn write_json(&self, path: impl AsRef<Path>) -> io::Result<()> {
        let file = File::create(path)?;
        serde_json::to_writer_pretty(file, self)?;
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct CaseTargetRecord {
    pub contract_id: usize,
    pub target_kind: String,
    pub producer_fn: Option<String>,
    pub sink_fn: String,
    pub std_fn: String,
    pub sp: String,
    pub family: String,
    pub effect_kind: Option<String>,
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
                StmtKind::Call(call) => Some(tcx.def_path_str(call.fn_did())),
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
