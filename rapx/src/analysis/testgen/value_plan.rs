use crate::analysis::testgen::context::{InputHint, NumericHint};
use crate::analysis::testgen::contract::{
    BinaryOp, ContractExpr, PredicateArg, PrimitiveSpKind, SafetyPredicate,
};
use rustc_middle::ty::{GenericArgKind, GenericArgsRef, Ty, TyCtxt, TyKind};
use rustc_type_ir::{FloatTy, IntTy, UintTy};
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ViolationGoal {
    NumericArg { arg_idx: usize, values: Vec<i128> },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ValuePlan {
    DirectArg {
        param_idx: usize,
        hint: InputHint,
        goal: ViolationGoal,
    },
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct TypeSizeEnv {
    sizes: BTreeMap<String, i128>,
}

impl TypeSizeEnv {
    pub fn from_generic_args<'tcx>(tcx: TyCtxt<'tcx>, args: GenericArgsRef<'tcx>) -> Self {
        let mut env = Self::default();
        let mut type_idx = 0usize;
        for arg in args.iter() {
            if let GenericArgKind::Type(ty) = arg.kind() {
                if let Some(size) = size_of_ty(tcx, ty) {
                    if type_idx == 0 {
                        env.sizes.insert("T".to_owned(), size);
                    }
                    env.sizes.insert(format!("T{type_idx}"), size);
                    env.sizes.insert(ty.to_string(), size);
                    type_idx += 1;
                }
            }
        }
        env
    }

    pub fn with_size(mut self, name: impl Into<String>, size: i128) -> Self {
        self.sizes.insert(name.into(), size);
        self
    }

    fn size_of(&self, name: &str) -> Option<i128> {
        self.sizes
            .get(name)
            .copied()
            .or_else(|| primitive_size(name))
    }
}

pub fn value_plans_for_valid_num_predicate(raw: &str, type_sizes: &TypeSizeEnv) -> Vec<ValuePlan> {
    let Some(goal) = violation_goal_for_valid_num_predicate(raw, type_sizes) else {
        return Vec::new();
    };
    let ViolationGoal::NumericArg { arg_idx, values } = &goal;
    let hints = values
        .iter()
        .copied()
        .map(numeric_hint_from_i128)
        .collect::<Vec<_>>();
    vec![ValuePlan::DirectArg {
        param_idx: *arg_idx,
        hint: InputHint::numeric(format!("violate {raw}"), hints),
        goal,
    }]
}

pub fn direct_numeric_hint_for_predicate(
    raw: &str,
    type_sizes: &TypeSizeEnv,
) -> Option<(usize, InputHint)> {
    let plan = value_plans_for_valid_num_predicate(raw, type_sizes)
        .into_iter()
        .next()?;
    match plan {
        ValuePlan::DirectArg {
            param_idx, hint, ..
        } => Some((param_idx, hint)),
    }
}

pub fn violation_goal_for_valid_num_predicate(
    raw: &str,
    type_sizes: &TypeSizeEnv,
) -> Option<ViolationGoal> {
    let predicate = SafetyPredicate::parse(raw).ok()?;
    if predicate.kind() != &PrimitiveSpKind::ValidNum {
        return None;
    }
    predicate.args().iter().find_map(|arg| match arg {
        PredicateArg::Expr(expr) => violation_goal_for_numeric_expr(expr, type_sizes),
        PredicateArg::Type(_) => None,
    })
}

fn violation_goal_for_numeric_expr(
    expr: &ContractExpr,
    type_sizes: &TypeSizeEnv,
) -> Option<ViolationGoal> {
    let ContractExpr::Binary { op, lhs, rhs } = expr else {
        return None;
    };
    if !matches!(
        op,
        BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge | BinaryOp::Eq | BinaryOp::Ne
    ) {
        return None;
    }

    let lhs_linear = linearize(lhs, type_sizes);
    let rhs_linear = linearize(rhs, type_sizes);
    match (lhs_linear, rhs_linear) {
        (Some(lhs), Some(rhs)) => solve_negated_comparison(*op, lhs, rhs),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct LinearExpr {
    arg_idx: Option<usize>,
    coeff: i128,
    constant: i128,
}

impl LinearExpr {
    fn constant(value: i128) -> Self {
        Self {
            arg_idx: None,
            coeff: 0,
            constant: value,
        }
    }

    fn arg(arg_idx: usize) -> Self {
        Self {
            arg_idx: Some(arg_idx),
            coeff: 1,
            constant: 0,
        }
    }

    fn add(self, rhs: Self) -> Option<Self> {
        let arg_idx = merge_arg_idx(self.arg_idx, rhs.arg_idx)?;
        Some(Self {
            arg_idx,
            coeff: self.coeff + rhs.coeff,
            constant: self.constant + rhs.constant,
        })
    }

    fn sub(self, rhs: Self) -> Option<Self> {
        let arg_idx = merge_arg_idx(self.arg_idx, rhs.arg_idx)?;
        Some(Self {
            arg_idx,
            coeff: self.coeff - rhs.coeff,
            constant: self.constant - rhs.constant,
        })
    }

    fn mul(self, rhs: Self) -> Option<Self> {
        match (self.arg_idx, rhs.arg_idx) {
            (Some(_), Some(_)) => None,
            (Some(arg_idx), None) => Some(Self {
                arg_idx: Some(arg_idx),
                coeff: self.coeff * rhs.constant,
                constant: self.constant * rhs.constant,
            }),
            (None, Some(arg_idx)) => Some(Self {
                arg_idx: Some(arg_idx),
                coeff: rhs.coeff * self.constant,
                constant: rhs.constant * self.constant,
            }),
            (None, None) => Some(Self::constant(self.constant * rhs.constant)),
        }
    }

    fn div(self, rhs: Self) -> Option<Self> {
        if rhs.arg_idx.is_some() || rhs.constant == 0 {
            return None;
        }
        Some(Self {
            arg_idx: self.arg_idx,
            coeff: self.coeff / rhs.constant,
            constant: self.constant / rhs.constant,
        })
    }
}

fn merge_arg_idx(lhs: Option<usize>, rhs: Option<usize>) -> Option<Option<usize>> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) if lhs != rhs => None,
        (Some(idx), _) | (_, Some(idx)) => Some(Some(idx)),
        (None, None) => Some(None),
    }
}

fn linearize(expr: &ContractExpr, type_sizes: &TypeSizeEnv) -> Option<LinearExpr> {
    match expr {
        ContractExpr::Arg(idx) => Some(LinearExpr::arg(*idx)),
        ContractExpr::Integer(raw) => parse_integer_literal(raw).map(LinearExpr::constant),
        ContractExpr::Const(raw) => parse_const_literal(raw).map(LinearExpr::constant),
        ContractExpr::SizeOf(name) => type_sizes.size_of(name).map(LinearExpr::constant),
        ContractExpr::Unary { expr, .. } => {
            let expr = linearize(expr, type_sizes)?;
            Some(LinearExpr {
                arg_idx: expr.arg_idx,
                coeff: -expr.coeff,
                constant: -expr.constant,
            })
        }
        ContractExpr::Binary { op, lhs, rhs } => {
            let lhs = linearize(lhs, type_sizes)?;
            let rhs = linearize(rhs, type_sizes)?;
            match op {
                BinaryOp::Add => lhs.add(rhs),
                BinaryOp::Sub => lhs.sub(rhs),
                BinaryOp::Mul => lhs.mul(rhs),
                BinaryOp::Div => lhs.div(rhs),
                _ => None,
            }
        }
    }
}

fn solve_negated_comparison(
    op: BinaryOp,
    lhs: LinearExpr,
    rhs: LinearExpr,
) -> Option<ViolationGoal> {
    let arg_idx = merge_arg_idx(lhs.arg_idx, rhs.arg_idx)??;
    let coeff = lhs.coeff - rhs.coeff;
    if coeff == 0 {
        return None;
    }
    let constant = lhs.constant - rhs.constant;
    let values = negated_values_for_linear(op, coeff, constant)?;
    Some(ViolationGoal::NumericArg { arg_idx, values })
}

fn negated_values_for_linear(op: BinaryOp, coeff: i128, constant: i128) -> Option<Vec<i128>> {
    // Comparison is `coeff * x + constant op 0`; values below violate it.
    let values = match op {
        BinaryOp::Ne => vec![div_floor(-constant, coeff)],
        BinaryOp::Eq => vec![div_floor(-constant, coeff).saturating_add(1)],
        BinaryOp::Lt => boundary_for_ge(coeff, constant),
        BinaryOp::Le => boundary_for_gt(coeff, constant),
        BinaryOp::Gt => boundary_for_le(coeff, constant),
        BinaryOp::Ge => boundary_for_lt(coeff, constant),
        _ => return None,
    };
    Some(values)
}

fn boundary_for_ge(coeff: i128, constant: i128) -> Vec<i128> {
    if coeff > 0 {
        let x = div_ceil(-constant, coeff);
        vec![x, x.saturating_add(1)]
    } else {
        let x = div_floor(-constant, coeff);
        vec![x, x.saturating_sub(1)]
    }
}

fn boundary_for_gt(coeff: i128, constant: i128) -> Vec<i128> {
    if coeff > 0 {
        vec![div_floor(-constant, coeff).saturating_add(1)]
    } else {
        vec![div_ceil(-constant, coeff).saturating_sub(1)]
    }
}

fn boundary_for_le(coeff: i128, constant: i128) -> Vec<i128> {
    if coeff > 0 {
        vec![div_floor(-constant, coeff)]
    } else {
        vec![div_ceil(-constant, coeff)]
    }
}

fn boundary_for_lt(coeff: i128, constant: i128) -> Vec<i128> {
    if coeff > 0 {
        vec![div_ceil(-constant, coeff).saturating_sub(1)]
    } else {
        vec![div_floor(-constant, coeff).saturating_add(1)]
    }
}

fn div_floor(lhs: i128, rhs: i128) -> i128 {
    let q = lhs / rhs;
    let r = lhs % rhs;
    if r != 0 && ((r > 0) != (rhs > 0)) {
        q - 1
    } else {
        q
    }
}

fn div_ceil(lhs: i128, rhs: i128) -> i128 {
    let q = lhs / rhs;
    let r = lhs % rhs;
    if r != 0 && ((r > 0) == (rhs > 0)) {
        q + 1
    } else {
        q
    }
}

fn parse_const_literal(raw: &str) -> Option<i128> {
    match raw {
        "isize::MAX" => Some(isize::MAX as i128),
        "usize::MAX" => Some(usize::MAX as i128),
        "i128::MAX" => Some(i128::MAX),
        "i64::MAX" => Some(i64::MAX as i128),
        "i32::MAX" => Some(i32::MAX as i128),
        "i16::MAX" => Some(i16::MAX as i128),
        "i8::MAX" => Some(i8::MAX as i128),
        "u64::MAX" => Some(u64::MAX as i128),
        "u32::MAX" => Some(u32::MAX as i128),
        "u16::MAX" => Some(u16::MAX as i128),
        "u8::MAX" => Some(u8::MAX as i128),
        _ => None,
    }
}

fn parse_integer_literal(raw: &str) -> Option<i128> {
    let digits = raw
        .chars()
        .take_while(|ch| ch.is_ascii_digit())
        .collect::<String>();
    if digits.is_empty() {
        None
    } else {
        digits.parse().ok()
    }
}

fn numeric_hint_from_i128(value: i128) -> NumericHint {
    match value {
        0 => NumericHint::Zero,
        1 => NumericHint::One,
        3 => NumericHint::Three,
        -1 => NumericHint::NegativeOne,
        _ => NumericHint::Literal(value),
    }
}

fn primitive_size(name: &str) -> Option<i128> {
    match name {
        "bool" | "i8" | "u8" => Some(1),
        "i16" | "u16" => Some(2),
        "i32" | "u32" | "f32" | "char" => Some(4),
        "i64" | "u64" | "f64" | "isize" | "usize" => Some(8),
        "i128" | "u128" => Some(16),
        _ => None,
    }
}

fn size_of_ty<'tcx>(_tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<i128> {
    match ty.kind() {
        TyKind::Bool => Some(1),
        TyKind::Char => Some(4),
        TyKind::Int(IntTy::I8) | TyKind::Uint(UintTy::U8) => Some(1),
        TyKind::Int(IntTy::I16) | TyKind::Uint(UintTy::U16) => Some(2),
        TyKind::Int(IntTy::I32) | TyKind::Uint(UintTy::U32) | TyKind::Float(FloatTy::F32) => {
            Some(4)
        }
        TyKind::Int(IntTy::I64)
        | TyKind::Uint(UintTy::U64)
        | TyKind::Int(IntTy::Isize)
        | TyKind::Uint(UintTy::Usize)
        | TyKind::Float(FloatTy::F64) => Some(8),
        TyKind::Int(IntTy::I128) | TyKind::Uint(UintTy::U128) => Some(16),
        TyKind::Array(inner, len) => {
            let len = len.try_to_target_usize(_tcx)? as i128;
            Some(size_of_ty(_tcx, *inner)? * len)
        }
        TyKind::Ref(..) | TyKind::RawPtr(..) => Some(8),
        _ => primitive_size(&ty.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_num_not_equal_zero_becomes_zero_goal() {
        let env = TypeSizeEnv::default();
        assert_eq!(
            violation_goal_for_valid_num_predicate("ValidNum(arg1 != 0)", &env),
            Some(ViolationGoal::NumericArg {
                arg_idx: 1,
                values: vec![0],
            })
        );
    }

    #[test]
    fn valid_num_size_of_expr_becomes_overflow_boundary() {
        let env = TypeSizeEnv::default().with_size("T", 16);
        let expected = (isize::MAX as i128) / 16 + 1;
        assert_eq!(
            violation_goal_for_valid_num_predicate(
                "ValidNum(arg1 * size_of(T) <= isize::MAX)",
                &env
            ),
            Some(ViolationGoal::NumericArg {
                arg_idx: 1,
                values: vec![expected],
            })
        );
    }

    #[test]
    fn value_plan_preserves_target_arg() {
        let env = TypeSizeEnv::default();
        let plans = value_plans_for_valid_num_predicate("ValidNum(arg2 < 3)", &env);
        assert_eq!(plans.len(), 1);
        let ValuePlan::DirectArg {
            param_idx,
            hint,
            goal,
        } = &plans[0];
        assert_eq!(*param_idx, 2);
        assert_eq!(
            *goal,
            ViolationGoal::NumericArg {
                arg_idx: 2,
                values: vec![3, 4],
            }
        );
        assert!(matches!(
            hint.kind,
            crate::analysis::testgen::context::InputHintKind::Numeric(_)
        ));
    }
}
