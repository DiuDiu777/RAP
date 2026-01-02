use crate::analysis::core::alias_analysis::default::types::TyKind;
use rustc_data_structures::fx::FxHashMap;

#[derive(Debug, Clone)]
pub struct Value {
    pub index: usize, // node index; this could be the field of a value.
    pub local: usize, // This is the real local; The range of index is generally larger than local.
    pub need_drop: bool,
    pub may_drop: bool,
    pub kind: TyKind,
    pub father: Option<FatherInfo>, // Use to indicate whether the value is a field of its father node:
    pub fields: FxHashMap<usize, usize>, // 1: field_id; 2: field_value_id;
}

#[derive(Debug, Clone, PartialEq)]
pub struct FatherInfo {
    pub father_value_id: usize,
    pub field_id: usize,
}

impl FatherInfo {
    pub fn new(father_value_id: usize, field_id: usize) -> Self {
        FatherInfo {
            father_value_id,
            field_id,
        }
    }
}

impl Value {
    pub fn new(index: usize, local: usize, need_drop: bool, may_drop: bool) -> Self {
        Value {
            index,
            local,
            need_drop,
            may_drop,
            kind: TyKind::Adt,
            father: None,
            fields: FxHashMap::default(),
        }
    }

    pub fn is_tuple(&self) -> bool {
        self.kind == TyKind::Tuple
    }

    pub fn is_ptr(&self) -> bool {
        self.kind == TyKind::RawPtr || self.kind == TyKind::Ref
    }

    pub fn is_ref(&self) -> bool {
        self.kind == TyKind::Ref
    }

    pub fn is_corner_case(&self) -> bool {
        self.kind == TyKind::CornerCase
    }
}
