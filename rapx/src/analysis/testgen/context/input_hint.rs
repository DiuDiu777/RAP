use rand::prelude::IndexedRandom;
use rand::Rng;
use rustc_type_ir::{IntTy, UintTy};

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
pub enum NumericHint {
    Zero,
    One,
    Three,
    Max,
    NegativeOne,
    Literal(i128),
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub enum InputHintKind {
    Numeric(Vec<NumericHint>),
    InvalidIndex,
    InvalidAlign,
    NullPtr,
    DanglingPtr,
    MisalignedPtr,
    UninitValue,
    InvalidUtf8,
    InvalidCStr,
    NoneVariant,
    ErrVariant,
    OverlappingRange,
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct InputHint {
    pub reason: String,
    pub kind: InputHintKind,
}

impl InputHint {
    pub fn numeric(reason: impl Into<String>, hints: Vec<NumericHint>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::Numeric(hints),
        }
    }

    pub fn invalid_index(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::InvalidIndex,
        }
    }

    pub fn invalid_align(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::InvalidAlign,
        }
    }

    pub fn invalid_unicode_scalar(reason: impl Into<String>) -> Self {
        Self::invalid_utf8(reason)
    }

    pub fn negative_offset(reason: impl Into<String>) -> Self {
        Self::numeric(reason, vec![NumericHint::NegativeOne, NumericHint::Max])
    }

    pub fn null_ptr(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::NullPtr,
        }
    }

    pub fn dangling_ptr(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::DanglingPtr,
        }
    }

    pub fn misaligned_ptr(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::MisalignedPtr,
        }
    }

    pub fn uninit_value(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::UninitValue,
        }
    }

    pub fn invalid_utf8(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::InvalidUtf8,
        }
    }

    pub fn invalid_cstr(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::InvalidCStr,
        }
    }

    pub fn none_variant(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::NoneVariant,
        }
    }

    pub fn err_variant(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::ErrVariant,
        }
    }

    pub fn overlapping_range(reason: impl Into<String>) -> Self {
        Self {
            reason: reason.into(),
            kind: InputHintKind::OverlappingRange,
        }
    }

    fn numeric_candidates(&self) -> Vec<NumericHint> {
        match &self.kind {
            InputHintKind::Numeric(hints) => hints.clone(),
            InputHintKind::InvalidIndex => vec![NumericHint::Max, NumericHint::Literal(1024)],
            InputHintKind::InvalidAlign => vec![NumericHint::Zero, NumericHint::Three],
            InputHintKind::NullPtr => vec![NumericHint::Zero],
            InputHintKind::DanglingPtr => vec![NumericHint::One],
            InputHintKind::MisalignedPtr => vec![NumericHint::Three],
            InputHintKind::InvalidUtf8 => {
                vec![NumericHint::Literal(0xD800), NumericHint::Literal(0x110000)]
            }
            InputHintKind::InvalidCStr => vec![NumericHint::One],
            InputHintKind::NoneVariant | InputHintKind::ErrVariant => vec![],
            InputHintKind::UninitValue => vec![NumericHint::Zero],
            InputHintKind::OverlappingRange => vec![NumericHint::One],
        }
    }
}

fn int_ty_name(int_ty: IntTy) -> &'static str {
    match int_ty {
        IntTy::Isize => "isize",
        IntTy::I8 => "i8",
        IntTy::I16 => "i16",
        IntTy::I32 => "i32",
        IntTy::I64 => "i64",
        IntTy::I128 => "i128",
    }
}

fn uint_ty_name(uint_ty: UintTy) -> &'static str {
    match uint_ty {
        UintTy::Usize => "usize",
        UintTy::U8 => "u8",
        UintTy::U16 => "u16",
        UintTy::U32 => "u32",
        UintTy::U64 => "u64",
        UintTy::U128 => "u128",
    }
}

fn max_int_expr(int_ty: IntTy) -> String {
    format!("{}::MAX", int_ty_name(int_ty))
}

fn max_uint_expr(uint_ty: UintTy) -> String {
    format!("{}::MAX", uint_ty_name(uint_ty))
}

fn clamp_signed_literal(value: i128, int_ty: IntTy) -> i128 {
    let bit_width = int_ty.bit_width().unwrap_or(64) as u32;
    let min = -(1i128 << (bit_width - 1));
    let max = (1i128 << (bit_width - 1)) - 1;
    value.clamp(min, max)
}

fn clamp_unsigned_literal(value: i128, uint_ty: UintTy) -> u128 {
    let bit_width = uint_ty.bit_width().unwrap_or(64) as u32;
    let max = if bit_width == 128 {
        u128::MAX
    } else {
        (1u128 << bit_width) - 1
    };
    if value < 0 {
        0
    } else {
        (value as u128).min(max)
    }
}

fn numeric_hint_for_int(hint: NumericHint, int_ty: IntTy) -> String {
    match hint {
        NumericHint::Zero => format!("0{}", int_ty_name(int_ty)),
        NumericHint::One => format!("1{}", int_ty_name(int_ty)),
        NumericHint::Three => format!("3{}", int_ty_name(int_ty)),
        NumericHint::Max => max_int_expr(int_ty),
        NumericHint::NegativeOne => format!("-1{}", int_ty_name(int_ty)),
        NumericHint::Literal(value) => {
            let value = clamp_signed_literal(value, int_ty);
            format!("{value}{}", int_ty_name(int_ty))
        }
    }
}

fn numeric_hint_for_uint(hint: NumericHint, uint_ty: UintTy) -> String {
    match hint {
        NumericHint::Zero => format!("0{}", uint_ty_name(uint_ty)),
        NumericHint::One => format!("1{}", uint_ty_name(uint_ty)),
        NumericHint::Three => format!("3{}", uint_ty_name(uint_ty)),
        NumericHint::Max | NumericHint::NegativeOne => max_uint_expr(uint_ty),
        NumericHint::Literal(value) => {
            let value = clamp_unsigned_literal(value, uint_ty);
            format!("{value}{}", uint_ty_name(uint_ty))
        }
    }
}

impl InputHint {
    pub fn gen_int<R: Rng>(&self, int_ty: IntTy, rng: &mut R) -> Option<String> {
        let hints = self.numeric_candidates();
        hints
            .as_slice()
            .choose(rng)
            .copied()
            .map(|hint| numeric_hint_for_int(hint, int_ty))
    }

    pub fn gen_uint<R: Rng>(&self, uint_ty: UintTy, rng: &mut R) -> Option<String> {
        let hints = self.numeric_candidates();
        hints
            .as_slice()
            .choose(rng)
            .copied()
            .map(|hint| numeric_hint_for_uint(hint, uint_ty))
    }
}
