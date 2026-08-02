/// Identifies a memory slot: a local variable with optional field projections.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Slot {
    pub local: usize,
    pub fields: Vec<usize>,
}

impl Slot {
    pub fn new(local: usize) -> Self {
        Slot {
            local,
            fields: Vec::new(),
        }
    }

    pub fn project(&self, field_idx: usize) -> Self {
        let mut fields = self.fields.clone();
        fields.push(field_idx);
        Slot {
            local: self.local,
            fields,
        }
    }
}

/// An abstract memory location a pointer can point to.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum AbstractLoc {
    Slot(Slot),
    Null,
}
