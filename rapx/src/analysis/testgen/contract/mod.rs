#![allow(dead_code, unused_imports)]

mod db;
mod primitive;

pub use db::{
    ContractDbError, ContractDbSummary, FunctionContract, SafetyContractDb, SafetyProperty,
};
pub use primitive::{normalize_tag, PrimitiveSpFamily, PrimitiveSpKind};

use std::fmt;

/// A source that can mutate state relevant to a lifted contract.
///
/// Public fields are modeled explicitly because generated client code can write
/// them even when no public setter API exists.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ContractMutationSource {
    ApiCall {
        fn_path: String,
    },
    PublicField {
        adt_path: String,
        field_name: String,
    },
}

impl fmt::Display for ContractMutationSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ApiCall { fn_path } => write!(f, "api:{fn_path}"),
            Self::PublicField {
                adt_path,
                field_name,
            } => write!(f, "public-field:{adt_path}.{field_name}"),
        }
    }
}
