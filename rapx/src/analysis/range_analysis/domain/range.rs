#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(irrefutable_let_patterns)]
use std::{default, fmt};

use num_traits::{Bounded, Num, Zero};
use rust_intervals::Interval;
use rustc_middle::mir::{BinOp, UnOp};
use std::ops::{Add, Mul, Sub};

use crate::{
    analysis::range_analysis::{Range, RangeType, domain::SymbolicExpr::IntervalTypeTrait},
    rap_trace,
};

use super::domain::*;

impl<T> Range<T>
where
    T: IntervalArithmetic,
{
    // Parameterized constructor
    pub fn new(lb: T, ub: T, rtype: RangeType) -> Self {
        Self {
            rtype,
            range: Interval::new_closed_closed(lb, ub),
        }
    }
    pub fn default(default: T) -> Self {
        Self {
            rtype: RangeType::Unknown,

            range: Interval::new_closed_closed(default, default),
        }
    }
    // Getter for lower bound
    pub fn init(r: Interval<T>) -> Self {
        Self {
            rtype: RangeType::Regular,
            range: r,
        }
    }
    pub fn get_lower(&self) -> T {
        self.range.lower().unwrap().clone()
    }

    // Getter for upper bound
    pub fn get_upper(&self) -> T {
        self.range.upper().unwrap().clone()
    }

    // Check if the range type is unknown
    pub fn is_unknown(&self) -> bool {
        self.rtype == RangeType::Unknown
    }

    // Set the range type to unknown
    pub fn set_unknown(&mut self) {
        self.rtype = RangeType::Unknown;
    }

    // Check if the range type is regular
    pub fn is_regular(&self) -> bool {
        self.rtype == RangeType::Regular
    }

    // Set the range type to regular
    pub fn set_regular(&mut self) {
        self.rtype = RangeType::Regular;
    }

    // Check if the range type is empty
    pub fn is_empty(&self) -> bool {
        self.rtype == RangeType::Empty
    }

    // Set the range type to empty
    pub fn set_empty(&mut self) {
        self.rtype = RangeType::Empty;
    }
    pub fn set_default(&mut self) {
        self.rtype = RangeType::Regular;
        self.range = Interval::new_closed_closed(T::min_value(), T::max_value());
    }
    pub fn add(&self, other: &Range<T>) -> Range<T> {
        let a = self
            .get_lower()
            .clone()
            .checked_add(&other.get_lower().clone())
            .unwrap_or(T::max_value());

        let b = self
            .get_upper()
            .clone()
            .checked_add(&other.get_upper().clone())
            .unwrap_or(T::max_value());

        Range::new(a, b, RangeType::Regular)
    }

    pub fn sub(&self, other: &Range<T>) -> Range<T> {
        let a = self
            .get_lower()
            .clone()
            .checked_sub(&other.get_upper().clone())
            .unwrap_or(T::min_value());

        let b = self
            .get_upper()
            .clone()
            .checked_sub(&other.get_lower().clone())
            .unwrap_or(T::max_value());

        Range::new(a, b, RangeType::Regular)
    }

    pub fn mul(&self, other: &Range<T>) -> Range<T> {
        let candidates = vec![
            self.get_lower().clone() * other.get_lower().clone(),
            self.get_lower().clone() * other.get_upper().clone(),
            self.get_upper().clone() * other.get_lower().clone(),
            self.get_upper().clone() * other.get_upper().clone(),
        ];
        let min = candidates
            .iter()
            .cloned()
            .min_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap();
        let max = candidates
            .iter()
            .cloned()
            .max_by(|a, b| a.partial_cmp(b).unwrap())
            .unwrap();
        Range::new(min, max, RangeType::Regular)
    }

    pub fn intersectwith(&self, other: &Range<T>) -> Range<T> {
        if self.is_unknown() {
            return Range::new(
                other.get_lower().clone(),
                other.get_upper().clone(),
                RangeType::Regular,
            );
        } else if other.is_unknown() {
            return Range::new(
                self.get_lower().clone(),
                self.get_upper().clone(),
                RangeType::Regular,
            );
        } else {
            let result = self.range.clone().intersection(&other.range.clone());
            let mut range = Range::default(T::min_value());

            if let r = result {
                range = Range::init(r);
                range
            } else {
                range
            }
        }
    }

    pub fn unionwith(&self, other: &Range<T>) -> Range<T> {
        if self.is_unknown() {
            return Range::new(
                other.get_lower().clone(),
                other.get_upper().clone(),
                RangeType::Regular,
            );
        } else if other.is_unknown() {
            return Range::new(
                self.get_lower().clone(),
                self.get_upper().clone(),
                RangeType::Regular,
            );
        } else {
            let left = std::cmp::min_by(self.get_lower(), other.get_lower(), |a, b| {
                a.partial_cmp(b).unwrap()
            });
            let right = std::cmp::max_by(self.get_upper(), other.get_upper(), |a, b| {
                a.partial_cmp(b).unwrap()
            });
            Range::new(left.clone(), right.clone(), RangeType::Regular)
        }
    }
}

// Implement the comparison operators
pub struct Meet;

impl Meet {
    pub fn widen<'tcx, T: IntervalArithmetic + ConstConvert>(
        op: &mut BasicOpKind<'tcx, T>,
        constant_vector: &[T],
        vars: &mut VarNodes<'tcx, T>,
    ) -> bool {
        // use crate::range_util::{get_first_less_from_vector, get_first_greater_from_vector};

        // assert!(!constant_vector.is_empty(), "Invalid constant vector");

        let old_interval = op.get_intersect().get_range().clone();
        let new_interval = op.eval(vars);
        let old_lower = old_interval.get_lower();
        let old_upper = old_interval.get_upper();
        let new_lower = new_interval.get_lower();
        let new_upper = new_interval.get_upper();
        let nlconstant = new_lower.clone();
        let nuconstant = new_upper.clone();
        let updated = if old_interval.is_unknown() {
            new_interval
        } else if new_lower < old_lower && new_upper > old_upper {
            Range::new(nlconstant, nuconstant, RangeType::Regular)
        } else if new_lower < old_lower {
            Range::new(nlconstant, old_upper.clone(), RangeType::Regular)
        } else if new_upper > old_upper {
            Range::new(old_lower.clone(), nuconstant, RangeType::Regular)
        } else {
            old_interval.clone()
        };

        op.set_intersect(updated.clone());
        let sink = op.get_sink();
        let new_sink_interval = op.get_intersect().get_range().clone();
        vars.get_mut(sink)
            .unwrap()
            .set_range(new_sink_interval.clone());
        rap_trace!(
            "WIDEN::{:?}: {:?} -> {:?}",
            sink,
            old_interval.range,
            new_sink_interval
        );
        old_interval.range != new_sink_interval.range
    }
    pub fn narrow<'tcx, T: IntervalArithmetic + ConstConvert>(
        op: &mut BasicOpKind<'tcx, T>,
        vars: &mut VarNodes<'tcx, T>,
    ) -> bool {
        let old_range = vars[op.get_sink()].get_range();
        let o_lower = old_range.get_lower().clone();
        let o_upper = old_range.get_upper().clone();

        let new_range = op.eval(vars);
        let n_lower = new_range.get_lower().clone();
        let n_upper = new_range.get_upper().clone();

        let mut has_changed = false;
        let min = T::min_value();
        let max = T::max_value();

        let mut result_lower = o_lower.clone();
        let mut result_upper = o_upper.clone();

        if o_lower == min && n_lower != min {
            result_lower = n_lower;
            has_changed = true;
        } else {
            // let smin = o_lower.clone().min(n_lower.clone());
            let smin = T::min_value();
            if o_lower != smin {
                result_lower = smin;
                has_changed = true;
            }
        }

        if o_upper == max && n_upper != max {
            result_upper = n_upper;
            has_changed = true;
        } else {
            // let smax = o_upper.clone().max(n_upper.clone());
            let smax = T::max_value();
            if o_upper != smax {
                result_upper = smax;
                has_changed = true;
            }
        }

        if has_changed {
            let new_sink_range = Range::new(
                result_lower.clone(),
                result_upper.clone(),
                RangeType::Regular,
            );
            let sink_node = vars.get_mut(op.get_sink()).unwrap();
            sink_node.set_range(new_sink_range.clone());

            // println!(
            //     "NARROW::{}: {:?} -> {:?}",
            // ,
            //     Range::new(o_lower, o_upper),
            //     new_sink_range
            // );
        }

        has_changed
    }
}
