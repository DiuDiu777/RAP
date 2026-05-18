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
    ) {
        self.eval_result = eval_result.into();
        self.compile_success = compile_success;
        self.miri_ub = miri_ub;
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
    pub lifted: usize,
    pub attempted: usize,
    pub ub: usize,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct CoverageTotals {
    pub lifted: usize,
    pub attempted: usize,
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
    attempted: BTreeSet<usize>,
    ub: BTreeSet<usize>,
}

impl ContractCoverage {
    pub fn new(instances: Vec<ContractInstanceRecord>) -> Self {
        Self {
            instances: instances
                .into_iter()
                .map(|instance| (instance.id, instance))
                .collect(),
            attempted: BTreeSet::new(),
            ub: BTreeSet::new(),
        }
    }

    pub fn record_case(&mut self, metadata: &CaseMetadata) {
        for target in &metadata.targets {
            if self.instances.contains_key(&target.contract_id) {
                self.attempted.insert(target.contract_id);
                if metadata.miri_ub {
                    self.ub.insert(target.contract_id);
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
                lifted: 0,
                attempted: 0,
                ub: 0,
            });
            sp_bucket.lifted += 1;
            if self.attempted.contains(id) {
                sp_bucket.attempted += 1;
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
                        lifted: 0,
                        attempted: 0,
                        ub: 0,
                    });
            family_bucket.lifted += 1;
            if self.attempted.contains(id) {
                family_bucket.attempted += 1;
            }
            if self.ub.contains(id) {
                family_bucket.ub += 1;
            }
        }

        ContractCoverageReport {
            totals: CoverageTotals {
                lifted: self.instances.len(),
                attempted: self.attempted.len(),
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
