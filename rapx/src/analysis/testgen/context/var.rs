use rustc_middle::ty;
use std::fmt::{self, Display};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var(pub usize, pub bool); // bool is true if the var is an input var

impl Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl Var {
    pub fn unique_id(&self) -> usize {
        self.0
    }
    pub fn is_from_input(&self) -> bool {
        self.1
    }
}

pub static DUMMY_INPUT_VAR: Var = Var(0, true);
pub static DUMMY_UNIT_VAR: Var = Var(0, false);
