use super::{Context, Stmt, UseKind, Var};
use rustc_middle::ty::{self, ParamEnv, Ty, TyCtxt, TypingMode};
use std::collections::VecDeque;
use std::fmt::{self, Display};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VarState {
    Live,
    Moved,
    Borrowed(usize),
    BorrowedMut,
    Dropped,
}

impl VarState {
    pub fn is_dropped(&self) -> bool {
        matches!(self, VarState::Dropped)
    }

    pub fn is_live(&self) -> bool {
        matches!(self, VarState::Live)
    }

    pub fn is_dead(&self) -> bool {
        matches!(self, VarState::Dropped | VarState::Moved)
    }

    pub fn is_borrowed(&self) -> bool {
        matches!(self, VarState::Borrowed(_) | VarState::BorrowedMut)
    }

    pub fn borrowed(mutability: ty::Mutability) -> Self {
        match mutability {
            ty::Mutability::Not => VarState::Borrowed(1),
            ty::Mutability::Mut => VarState::BorrowedMut,
        }
    }

    pub fn unborrowed(self) -> Option<Self> {
        match self {
            VarState::Borrowed(1) | VarState::BorrowedMut => Some(VarState::Live),
            VarState::Borrowed(cnt) => Some(VarState::Borrowed(cnt - 1)),
            _ => None,
        }
    }
}

impl Display for VarState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VarState::Live => write!(f, "Live"),
            VarState::Moved => write!(f, "Moved"),
            VarState::Borrowed(cnt) => write!(f, "Borrowed({cnt})"),
            VarState::BorrowedMut => write!(f, "BorrowedMut"),
            VarState::Dropped => write!(f, "Dropped"),
        }
    }
}

impl<'tcx> Context<'tcx> {
    pub fn var_state(&self, var: Var) -> VarState {
        self.var_state[&var]
    }

    pub fn set_var_state(&mut self, var: Var, state: VarState) -> VarState {
        let old_state = self
            .var_state
            .insert(var, state)
            .expect("var are expected always have a var state");
        if matches!(old_state, VarState::Moved | VarState::Dropped) {
            panic!("try to change the varstate of {var} from {old_state} to {state}");
        }

        old_state
    }

    pub fn unborrow_var(&mut self, var: Var) -> Option<VarState> {
        let state = self.var_state(var);
        state.unborrowed().inspect(|varstate| {
            self.set_var_state(var, *varstate);
        })
    }

    pub fn borrow_var(&mut self, var: Var, mutability: ty::Mutability) -> VarState {
        self.lift_mutability(var, mutability);
        let new_state = match self.var_state(var) {
            VarState::BorrowedMut => {
                assert!(mutability == ty::Mutability::Mut);
                VarState::BorrowedMut
            }
            VarState::Borrowed(cnt) => VarState::Borrowed(cnt + 1),
            _ => VarState::borrowed(mutability),
        };
        self.set_var_state(var, new_state)
    }
}
