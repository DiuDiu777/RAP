use super::primitive::{normalize_tag, PrimitiveSpFamily, PrimitiveSpKind};
use std::collections::BTreeMap;
use std::env;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

pub const CONTRACT_DB_ENV: &str = "TESTGEN_CONTRACT_DB";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SafetyProperty {
    raw_tag: String,
    kind: PrimitiveSpKind,
    disjunctive: bool,
}

impl SafetyProperty {
    pub fn from_raw_tag(raw_tag: impl Into<String>) -> Self {
        let raw_tag = raw_tag.into();
        let disjunctive = raw_tag.contains('|');
        let kind = PrimitiveSpKind::from_tag(&raw_tag);
        Self {
            raw_tag,
            kind,
            disjunctive,
        }
    }

    pub fn raw_tag(&self) -> &str {
        &self.raw_tag
    }

    pub fn normalized_tag(&self) -> String {
        normalize_tag(&self.raw_tag)
    }

    pub fn kind(&self) -> &PrimitiveSpKind {
        &self.kind
    }

    pub fn is_disjunctive(&self) -> bool {
        self.disjunctive
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionContract {
    function: String,
    sites: BTreeMap<usize, Vec<SafetyProperty>>,
}

impl FunctionContract {
    fn new(function: impl Into<String>) -> Self {
        Self {
            function: function.into(),
            sites: BTreeMap::new(),
        }
    }

    pub fn function(&self) -> &str {
        &self.function
    }

    pub fn sites(&self) -> &BTreeMap<usize, Vec<SafetyProperty>> {
        &self.sites
    }

    pub fn properties_at(&self, site: usize) -> Option<&[SafetyProperty]> {
        self.sites.get(&site).map(Vec::as_slice)
    }

    pub fn property_count(&self) -> usize {
        self.sites.values().map(Vec::len).sum()
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SafetyContractDb {
    functions: BTreeMap<String, FunctionContract>,
}

impl SafetyContractDb {
    pub fn from_json_str(input: &str) -> Result<Self, ContractDbError> {
        let raw: BTreeMap<String, BTreeMap<String, Vec<String>>> = serde_json::from_str(input)?;
        let mut db = Self::default();

        for (function, raw_sites) in raw {
            let mut contract = FunctionContract::new(function.clone());
            for (site, tags) in raw_sites {
                let site =
                    site.parse::<usize>()
                        .map_err(|_| ContractDbError::InvalidSiteIndex {
                            function: function.clone(),
                            site,
                        })?;
                let properties = tags
                    .into_iter()
                    .map(SafetyProperty::from_raw_tag)
                    .collect::<Vec<_>>();
                contract.sites.insert(site, properties);
            }
            db.functions.insert(function, contract);
        }

        Ok(db)
    }

    pub fn load_from_path(path: impl AsRef<Path>) -> Result<Self, ContractDbError> {
        let path = path.as_ref();
        let input = fs::read_to_string(path).map_err(|source| ContractDbError::Io {
            path: path.to_path_buf(),
            source,
        })?;
        Self::from_json_str(&input)
    }

    pub fn load_default() -> Result<Self, ContractDbError> {
        if let Ok(path) = env::var(CONTRACT_DB_ENV) {
            return Self::load_from_path(path);
        }

        let candidates = default_candidate_paths();
        for path in &candidates {
            if path.exists() {
                return Self::load_from_path(path);
            }
        }

        Err(ContractDbError::NotFound { candidates })
    }

    pub fn get(&self, function: &str) -> Option<&FunctionContract> {
        self.functions.get(function)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &FunctionContract)> {
        self.functions
            .iter()
            .map(|(function, contract)| (function.as_str(), contract))
    }

    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    pub fn site_count(&self) -> usize {
        self.functions
            .values()
            .map(|contract| contract.sites.len())
            .sum()
    }

    pub fn property_count(&self) -> usize {
        self.functions
            .values()
            .map(FunctionContract::property_count)
            .sum()
    }

    pub fn summary(&self) -> ContractDbSummary {
        let mut summary = ContractDbSummary {
            functions: self.function_count(),
            sites: self.site_count(),
            properties: self.property_count(),
            ..ContractDbSummary::default()
        };

        for contract in self.functions.values() {
            for properties in contract.sites.values() {
                for property in properties {
                    *summary.by_kind.entry(property.kind.clone()).or_default() += 1;
                    *summary.by_family.entry(property.kind.family()).or_default() += 1;
                    if property.is_disjunctive() {
                        summary.disjunctive_properties += 1;
                    }
                }
            }
        }

        summary
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ContractDbSummary {
    pub functions: usize,
    pub sites: usize,
    pub properties: usize,
    pub disjunctive_properties: usize,
    pub by_kind: BTreeMap<PrimitiveSpKind, usize>,
    pub by_family: BTreeMap<PrimitiveSpFamily, usize>,
}

impl ContractDbSummary {
    pub fn brief(&self) -> String {
        format!(
            "{} functions, {} sites, {} properties",
            self.functions, self.sites, self.properties
        )
    }

    pub fn to_report_string(&self) -> String {
        let mut report = String::new();
        report.push_str(&format!("functions = {}\n", self.functions));
        report.push_str(&format!("sites = {}\n", self.sites));
        report.push_str(&format!("properties = {}\n", self.properties));
        report.push_str(&format!(
            "disjunctive_properties = {}\n",
            self.disjunctive_properties
        ));

        report.push_str("\nby_family:\n");
        for (family, count) in &self.by_family {
            report.push_str(&format!("  {:?}: {}\n", family, count));
        }

        report.push_str("\nby_kind:\n");
        for (kind, count) in &self.by_kind {
            report.push_str(&format!("  {}: {}\n", kind, count));
        }

        report
    }
}

#[derive(Debug)]
pub enum ContractDbError {
    Io { path: PathBuf, source: io::Error },
    Json(serde_json::Error),
    InvalidSiteIndex { function: String, site: String },
    NotFound { candidates: Vec<PathBuf> },
}

impl fmt::Display for ContractDbError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, source } => {
                write!(f, "failed to read {}: {}", path.display(), source)
            }
            Self::Json(err) => write!(f, "failed to parse contract database: {err}"),
            Self::InvalidSiteIndex { function, site } => {
                write!(f, "invalid contract site index `{site}` for {function}")
            }
            Self::NotFound { candidates } => {
                write!(
                    f,
                    "cannot find std contract database; set {CONTRACT_DB_ENV} or place it at one of: {}",
                    candidates
                        .iter()
                        .map(|path| path.display().to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

impl std::error::Error for ContractDbError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::Json(err) => Some(err),
            Self::InvalidSiteIndex { .. } | Self::NotFound { .. } => None,
        }
    }
}

impl From<serde_json::Error> for ContractDbError {
    fn from(err: serde_json::Error) -> Self {
        Self::Json(err)
    }
}

fn default_candidate_paths() -> Vec<PathBuf> {
    let mut candidates = Vec::new();

    if let Ok(current_dir) = env::current_dir() {
        push_ancestor_candidates(&mut candidates, &current_dir);
    }

    if let Ok(manifest_dir) = env::var("CARGO_MANIFEST_DIR") {
        push_ancestor_candidates(&mut candidates, Path::new(&manifest_dir));
    }

    candidates
}

fn push_ancestor_candidates(candidates: &mut Vec<PathBuf>, start: &Path) {
    for ancestor in start.ancestors() {
        let path = ancestor.join("safety-tags").join("data").join("std.json");
        if !candidates.contains(&path) {
            candidates.push(path);
        }
    }
}
