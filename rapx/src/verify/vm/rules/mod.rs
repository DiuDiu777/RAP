//! Abstract-interpretation rules for the symbolic VM, defined in one place.
//!
//! The three MIR construct families the VM executes — `Statement`, `Rvalue`,
//! and `Terminator` — are each described by a registry of named rules.  A rule
//! is a `(name, apply)` pair: `apply` both classifies the construct (returning
//! `None`/`false` when it does not handle it, so the executor tries the next
//! rule) and performs its effect when it does.  The executors only walk the
//! tables, so the semantics live here rather than in a `match` inside an
//! `impl VmState`.

use rustc_middle::mir::{BasicBlock, Place, Rvalue, Statement, Terminator};

use super::state::{VmState, VmValue};

pub(crate) mod rvalue;
pub(crate) mod statement;
pub(crate) mod terminator;

/// A rule interpreting an `Rvalue`: evaluate it into the destination's value,
/// or return `None` to decline and let the next rule try.
pub(crate) struct RvalueRule {
    /// Rule name, for logging / hit-statistics / debugging.
    pub name: &'static str,
    /// The transfer function: `Some(value)` when it handled `rvalue`, `None`
    /// otherwise.
    pub apply: for<'z3, 'tcx> fn(
        &mut VmState<'z3, 'tcx>,
        &Place<'tcx>,
        &Rvalue<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>>,
}

/// A rule interpreting a `Terminator`: apply its effect (`Call`, `SwitchInt`,
/// `Assert`, `Drop`, or no-op) and return `true`, or return `false` to decline.
pub(crate) struct TerminatorRule {
    pub name: &'static str,
    pub apply:
        for<'z3, 'tcx> fn(&mut VmState<'z3, 'tcx>, &Terminator<'tcx>, Option<BasicBlock>) -> bool,
}

/// A rule interpreting a `Statement`: apply its effect (`Assign`,
/// `StorageLive`/`StorageDead`, or no-op) and return `true`, or `false` to
/// decline.
pub(crate) struct StatementRule {
    pub name: &'static str,
    pub apply: for<'z3, 'tcx> fn(&mut VmState<'z3, 'tcx>, &Statement<'tcx>) -> bool,
}

/// Every `Rvalue` rule, in dispatch order.
pub(crate) const RVALUE_RULES: &[RvalueRule] = &[
    RvalueRule { name: "use", apply: rvalue::eval_use },
    RvalueRule { name: "ref", apply: rvalue::eval_ref },
    RvalueRule { name: "raw_ptr", apply: rvalue::eval_raw_ptr },
    RvalueRule { name: "binary_op", apply: rvalue::eval_binary_op },
    RvalueRule { name: "unary_op", apply: rvalue::eval_unary_op },
    RvalueRule { name: "cast", apply: rvalue::eval_cast },
    RvalueRule { name: "aggregate", apply: rvalue::eval_aggregate },
    RvalueRule { name: "discriminant", apply: rvalue::eval_discriminant },
    #[cfg(not(rapx_ge_99))]
    RvalueRule { name: "shallow_init_box", apply: rvalue::eval_shallow_init_box },
    RvalueRule { name: "copy_for_deref", apply: rvalue::eval_copy_for_deref },
    RvalueRule { name: "repeat", apply: rvalue::eval_repeat },
    RvalueRule { name: "thread_local_ref", apply: rvalue::eval_thread_local_ref },
    #[cfg(not(rapx_ge_95))]
    RvalueRule { name: "nullary_op", apply: rvalue::eval_nullary_op },
    RvalueRule { name: "wrap_unsafe_binder", apply: rvalue::eval_wrap_unsafe_binder },
    #[cfg(rapx_rvalue_has_reborrow)]
    RvalueRule { name: "reborrow", apply: rvalue::eval_reborrow },
];

/// Every `Terminator` rule, in dispatch order.
pub(crate) const TERMINATOR_RULES: &[TerminatorRule] = &[
    TerminatorRule { name: "call", apply: terminator::exec_call },
    TerminatorRule { name: "switch_int", apply: terminator::exec_switch_int },
    TerminatorRule { name: "assert", apply: terminator::exec_assert },
    TerminatorRule { name: "drop", apply: terminator::exec_drop },
    TerminatorRule { name: "nop", apply: terminator::exec_nop },
];

/// Every `Statement` rule, in dispatch order.
pub(crate) const STATEMENT_RULES: &[StatementRule] = &[
    StatementRule { name: "assign", apply: statement::exec_assign },
    StatementRule { name: "storage_live", apply: statement::exec_storage_live },
    StatementRule { name: "storage_dead", apply: statement::exec_storage_dead },
    StatementRule { name: "nop", apply: statement::exec_nop },
];

/// Evaluate an `Rvalue` by walking [`RVALUE_RULES`] until one accepts it.
pub(crate) fn eval_rvalue<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> VmValue<'z3, 'tcx> {
    for rule in RVALUE_RULES {
        if let Some(value) = (rule.apply)(state, place, rvalue) {
            crate::rap_debug!("rvalue rule: {}", rule.name);
            return value;
        }
    }
    unreachable!("no rule for rvalue: {:?}", rvalue)
}

/// Execute a `Terminator` by walking [`TERMINATOR_RULES`] until one accepts it.
pub(crate) fn exec_terminator<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    terminator: &Terminator<'tcx>,
    switch_succ: Option<BasicBlock>,
) {
    for rule in TERMINATOR_RULES {
        if (rule.apply)(state, terminator, switch_succ) {
            crate::rap_debug!("terminator rule: {}", rule.name);
            return;
        }
    }
    unreachable!("no rule for terminator: {:?}", terminator.kind)
}

/// Execute a `Statement` by walking [`STATEMENT_RULES`] until one accepts it.
pub(crate) fn exec_statement<'z3, 'tcx>(state: &mut VmState<'z3, 'tcx>, statement: &Statement<'tcx>) {
    for rule in STATEMENT_RULES {
        if (rule.apply)(state, statement) {
            crate::rap_debug!("statement rule: {}", rule.name);
            return;
        }
    }
    unreachable!("no rule for statement: {:?}", statement.kind)
}
