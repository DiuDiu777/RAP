use crate::analysis::alias::default::types::ValueKind;
use crate::compat::FxHashMap;

#[derive(Debug, Clone)]
pub struct Value {
    pub index: usize,
    pub local: usize,
    pub kind: ValueKind,
    pub father: Option<FatherInfo>,
    pub fields: FxHashMap<usize, usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FatherInfo {
    pub father_value_id: usize,
    pub field_id: usize,
}

impl FatherInfo {
    pub fn new(father_value_id: usize, field_id: usize) -> Self {
        FatherInfo { father_value_id, field_id }
    }
}

impl Value {
    pub fn new(index: usize, local: usize) -> Self {
        Value {
            index, local,
            kind: ValueKind::Adt,
            father: None,
            fields: FxHashMap::default(),
        }
    }

    pub fn is_ptr(&self) -> bool {
        self.kind == ValueKind::RawPtr || self.kind == ValueKind::Ref
    }

    pub fn is_ref_count(&self) -> bool {
        self.kind == ValueKind::SpecialPtr
    }
}
