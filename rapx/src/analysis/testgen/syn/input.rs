use rand::{rngs::ThreadRng, seq::IndexedRandom, Rng};
use rustc_abi::FIRST_VARIANT;
use rustc_hir::LangItem;
use rustc_middle::ty::{AdtDef, GenericArgsRef, Mutability, Ty, TyCtxt, TyKind};
use rustc_span::sym;
use rustc_type_ir::{IntTy, UintTy};
use std::ops::Range;

use crate::analysis::testgen::{
    context::{InputHint, InputHintKind},
    path::PathResolver,
};

// fn int_ty_suffix()

pub trait InputGen {
    fn gen_bool(&mut self) -> bool;
    fn gen_int(&mut self, int_ty: IntTy) -> i64;
    fn gen_uint(&mut self, uint_ty: UintTy) -> u64;
    fn gen_float(&mut self) -> f32;
    fn gen_char(&mut self) -> char;
    fn gen_str(&mut self) -> String;
    fn gen_adt<'tcx>(
        &mut self,
        adt_def: AdtDef<'tcx>,
        args: GenericArgsRef<'tcx>,
        tcx: TyCtxt<'tcx>,
        resolver: &PathResolver<'tcx>,
    ) -> String;

    fn gen_custom<'tcx>(
        &mut self,
        ty: Ty<'tcx>,
        tcx: TyCtxt<'tcx>,
        resolver: &PathResolver<'tcx>,
    ) -> Option<String> {
        None
    }

    fn gen<'tcx>(
        &mut self,
        ty: Ty<'tcx>,
        tcx: TyCtxt<'tcx>,
        resolver: &PathResolver<'tcx>,
    ) -> String {
        if let Some(s) = self.gen_custom(ty, tcx, resolver) {
            return s;
        }

        match ty.kind() {
            TyKind::Ref(_, inner_ty, mutability) => {
                if inner_ty.is_str() && mutability.is_not() {
                    return format!("\"{}\"", self.gen_str());
                }
                format!(
                    "{}{}",
                    mutability.ref_prefix_str(),
                    self.gen(*inner_ty, tcx, resolver)
                )
            }
            TyKind::Bool => self.gen_bool().to_string(),
            TyKind::Int(int_ty) => {
                format!("{}{}", self.gen_int(*int_ty).to_string(), int_ty.name_str())
            }
            TyKind::Uint(uint_ty) => {
                format!(
                    "{}{}",
                    self.gen_uint(*uint_ty).to_string(),
                    uint_ty.name_str()
                )
            }
            TyKind::Float(float_ty) => {
                format!("{}{}", self.gen_float().to_string(), float_ty.name_str())
            }
            TyKind::Char => format!("'{}'", self.gen_char()),
            TyKind::Str => {
                unreachable!("str should be referenced as &str");
            }
            TyKind::Array(inner_ty, const_) => {
                let len = match const_.kind() {
                    rustc_type_ir::ConstKind::Value(value) => value
                        .try_to_target_usize(tcx)
                        .expect("cannot conver to target usize"),
                    _ => {
                        unreachable!("unexpected const kind: {}", const_);
                    }
                };

                let mut arr: Vec<String> = Vec::new();
                for _ in 0..len {
                    arr.push(self.gen(*inner_ty, tcx, resolver).to_string());
                }
                format!("[{}]", arr.join(", "))
            }
            TyKind::Tuple(tys) => {
                let mut fields = Vec::new();
                for ty in tys.iter() {
                    fields.push(self.gen(ty, tcx, resolver).to_string());
                }
                format!("({})", fields.join(", "))
            }
            TyKind::Adt(adt_def, generic_args) => {
                self.gen_adt(*adt_def, generic_args, tcx, resolver)
            }
            TyKind::Slice(inner_ty) => {
                let len = 3; // Fixed length for simplicity
                let element = self.gen(*inner_ty, tcx, resolver).to_string();
                format!("[{}; {}]", element, len)
            }
            _ => panic!("Unsupported type: {:?}", ty),
        }
    }

    fn gen_with_hint<'tcx>(
        &mut self,
        ty: Ty<'tcx>,
        hint: Option<&InputHint>,
        tcx: TyCtxt<'tcx>,
        resolver: &PathResolver<'tcx>,
    ) -> String {
        let _ = hint;
        self.gen(ty, tcx, resolver)
    }
}

pub struct SillyInputGen;

impl InputGen for SillyInputGen {
    fn gen_bool(&mut self) -> bool {
        false
    }

    fn gen_int(&mut self, int_ty: IntTy) -> i64 {
        42
    }

    fn gen_uint(&mut self, uint_ty: UintTy) -> u64 {
        42
    }

    fn gen_float(&mut self) -> f32 {
        42.0
    }

    fn gen_char(&mut self) -> char {
        'a'
    }

    fn gen_str(&mut self) -> String {
        "don't panic".to_owned()
    }

    fn gen_adt<'tcx>(
        &mut self,
        adt_def: AdtDef<'tcx>,
        args: GenericArgsRef<'tcx>,
        tcx: TyCtxt<'tcx>,
        resolver: &PathResolver<'tcx>,
    ) -> String {
        let name = resolver.path_str_with_args(adt_def.did(), args);
        if adt_def.is_struct() {
            // generate input for each field
            let mut fields = Vec::new();
            for field in adt_def.all_fields() {
                let field_name = field.name.to_string();
                let field_type = field.ty(tcx, args);
                let field_input = self.gen(field_type, tcx, resolver).to_string();
                fields.push(format!("{field_name}: {field_input}"));
            }
            return format!("{name} {{ {} }}", fields.join(", "));
        }
        if adt_def.is_enum() {
            let mut fields = Vec::new();
            // Always generate the first variant

            let variant_def = adt_def.variant(FIRST_VARIANT);
            let variant_name = variant_def.name.to_string();
            for field in variant_def.fields.iter() {
                let field_name = field.name.to_string();
                let field_type = field.ty(tcx, args);
                let field_input = self.gen(field_type, tcx, resolver).to_string();
                fields.push(format!("{field_name}: {field_input}"));
            }
            if fields.is_empty() {
                return format!("{name}::{variant_name}");
            }
            return format!("{name}::{variant_name} {{ {} }}", fields.join(", "));
        }
        panic!("Unsupported ADT ({:?},{:?})", adt_def, args)
    }
}

pub struct RandomGen<R: Rng> {
    rng: R,
}

impl RandomGen<ThreadRng> {
    pub fn new() -> RandomGen<ThreadRng> {
        RandomGen { rng: rand::rng() }
    }
}

fn range_for_int_ty(int_ty: IntTy) -> Range<i64> {
    let bit_width = int_ty.bit_width().unwrap_or(32) as u32;
    -(2i64.pow(bit_width - 1))..2i64.pow(bit_width - 1) - 1
}

fn range_for_uint_ty(uint_ty: UintTy) -> Range<u64> {
    let bit_width = uint_ty.bit_width().unwrap_or(32) as u32;
    0..2u64.pow(bit_width) - 1
}

fn gen_random_utf8_seq<R: Rng>(rng: &mut R, min_len: usize, max_len: usize) -> String {
    let len = rng.random_range(min_len..=max_len);
    rng.random_iter::<char>().take(len).collect()
}

fn ty_is_u8(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Uint(UintTy::U8))
}

fn array_len<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Option<u64> {
    if let TyKind::Array(_, const_) = ty.kind() {
        if let rustc_type_ir::ConstKind::Value(value) = const_.kind() {
            return value.try_to_target_usize(tcx);
        }
    }
    None
}

fn byte_exprs(bytes: &[u8]) -> Vec<String> {
    bytes.iter().map(|byte| format!("0x{byte:02x}u8")).collect()
}

fn byte_vec_expr(bytes: &[u8]) -> String {
    format!("vec![{}]", byte_exprs(bytes).join(", "))
}

fn byte_array_expr(bytes: &[u8], len: u64) -> String {
    let len = len as usize;
    if len == 0 {
        return "[]".to_string();
    }

    let mut elements = Vec::with_capacity(len);
    for idx in 0..len {
        elements.push(bytes[idx % bytes.len()]);
    }
    format!("[{}]", byte_exprs(&elements).join(", "))
}

fn byte_string_literal(bytes: &[u8]) -> String {
    let mut literal = String::from("b\"");
    for byte in bytes {
        match *byte {
            b'\\' => literal.push_str("\\\\"),
            b'"' => literal.push_str("\\\""),
            0x20..=0x7e => literal.push(*byte as char),
            _ => literal.push_str(&format!("\\x{byte:02x}")),
        }
    }
    literal.push('"');
    literal
}

fn byte_slice_expr(bytes: &[u8], mutability: Mutability) -> String {
    let elements = byte_exprs(bytes).join(", ");
    match mutability {
        Mutability::Mut => format!("&mut [{elements}][..]"),
        Mutability::Not => format!("&[{elements}][..]"),
    }
}

fn raw_ptr_cast_expr<'tcx>(
    address: usize,
    inner_ty: Ty<'tcx>,
    mutability: Mutability,
    resolver: &PathResolver<'tcx>,
) -> String {
    if address == 0 {
        return null_ptr_expr(inner_ty, mutability, resolver);
    }

    let inner = resolver.ty_str(inner_ty);
    let dangling = format!("std::ptr::NonNull::<{inner}>::dangling().as_ptr()");
    match mutability {
        Mutability::Mut => dangling,
        Mutability::Not => format!("{dangling} as *const {inner}"),
    }
}

fn null_ptr_expr<'tcx>(
    inner_ty: Ty<'tcx>,
    mutability: Mutability,
    resolver: &PathResolver<'tcx>,
) -> String {
    let inner = resolver.ty_str(inner_ty);
    match mutability {
        Mutability::Mut => format!("std::ptr::null_mut::<{inner}>()"),
        Mutability::Not => format!("std::ptr::null::<{inner}>()"),
    }
}

fn cstr_raw_ptr_expr<'tcx>(
    inner_ty: Ty<'tcx>,
    mutability: Mutability,
    resolver: &PathResolver<'tcx>,
) -> String {
    let ptr_kind = match mutability {
        Mutability::Mut => "*mut",
        Mutability::Not => "*const",
    };
    format!(
        "b\"unterminated\".as_ptr() as {ptr_kind} {}",
        resolver.ty_str(inner_ty)
    )
}

fn adt_path_contains<'tcx>(tcx: TyCtxt<'tcx>, adt_def: AdtDef<'tcx>, needle: &str) -> bool {
    tcx.def_path_str(adt_def.did()).contains(needle)
}

fn is_maybe_uninit<'tcx>(tcx: TyCtxt<'tcx>, adt_def: AdtDef<'tcx>) -> bool {
    tcx.item_name(adt_def.did()).as_str() == "MaybeUninit" && adt_path_contains(tcx, adt_def, "mem")
}

fn is_range<'tcx>(tcx: TyCtxt<'tcx>, adt_def: AdtDef<'tcx>) -> bool {
    adt_path_contains(tcx, adt_def, "ops::range::Range")
}

fn zero_one_range_for_ty(ty: Ty<'_>) -> Option<String> {
    match ty.kind() {
        TyKind::Int(int_ty) => Some(format!("0{}..1{}", int_ty.name_str(), int_ty.name_str())),
        TyKind::Uint(uint_ty) => Some(format!("0{}..1{}", uint_ty.name_str(), uint_ty.name_str())),
        TyKind::Float(float_ty) => Some(format!(
            "0.0{}..1.0{}",
            float_ty.name_str(),
            float_ty.name_str()
        )),
        _ => None,
    }
}

fn hinted_bytes_expr<'tcx>(
    ty: Ty<'tcx>,
    bytes: &[u8],
    tcx: TyCtxt<'tcx>,
    resolver: &PathResolver<'tcx>,
) -> Option<String> {
    match ty.kind() {
        TyKind::Adt(adt_def, args) if tcx.is_diagnostic_item(sym::Vec, adt_def.did()) => {
            if ty_is_u8(args.type_at(0)) {
                return Some(byte_vec_expr(bytes));
            }
        }
        TyKind::Array(inner_ty, _) if ty_is_u8(*inner_ty) => {
            return Some(byte_array_expr(bytes, array_len(ty, tcx)?));
        }
        TyKind::Slice(inner_ty) if ty_is_u8(*inner_ty) => {
            return Some(byte_array_expr(bytes, bytes.len() as u64));
        }
        TyKind::Ref(_, inner_ty, mutability) => match inner_ty.kind() {
            TyKind::Slice(slice_ty) if ty_is_u8(*slice_ty) => {
                return Some(byte_slice_expr(bytes, *mutability));
            }
            TyKind::Array(array_ty, _) if ty_is_u8(*array_ty) => {
                let len = array_len(*inner_ty, tcx)?;
                let array = byte_array_expr(bytes, len);
                return Some(match mutability {
                    Mutability::Mut => format!("&mut {array}"),
                    Mutability::Not => format!("&{array}"),
                });
            }
            _ => {}
        },
        TyKind::RawPtr(inner_ty, mutability) => {
            let bytes = byte_string_literal(bytes);
            return Some(match mutability {
                Mutability::Mut => {
                    format!("{bytes}.as_ptr() as *mut {}", resolver.ty_str(*inner_ty))
                }
                Mutability::Not => {
                    format!("{bytes}.as_ptr() as *const {}", resolver.ty_str(*inner_ty))
                }
            });
        }
        _ => {}
    }
    None
}

impl<R: Rng> InputGen for RandomGen<R> {
    fn gen_bool(&mut self) -> bool {
        self.rng.random()
    }

    fn gen_int(&mut self, int_ty: IntTy) -> i64 {
        self.rng.random_range(range_for_int_ty(IntTy::I8))
    }

    fn gen_uint(&mut self, uint_ty: UintTy) -> u64 {
        self.rng.random_range(range_for_uint_ty(UintTy::U8))
    }

    fn gen_float(&mut self) -> f32 {
        self.rng.random()
    }

    fn gen_char(&mut self) -> char {
        gen_random_utf8_seq(&mut self.rng, 1, 1)
            .chars()
            .nth(0)
            .unwrap()
    }

    fn gen_str(&mut self) -> String {
        gen_random_utf8_seq(&mut self.rng, 0, 16)
    }

    fn gen_custom<'tcx>(
        &mut self,
        ty: Ty<'tcx>,
        tcx: TyCtxt<'tcx>,
        resolver: &PathResolver<'tcx>,
    ) -> Option<String> {
        if let TyKind::Adt(adt_def, args) = ty.kind() {
            let did = adt_def.did();
            if tcx.is_lang_item(did, LangItem::String) {
                return Some(format!("String::from(\"{}\")", self.gen_str()));
            }
            if tcx.is_diagnostic_item(sym::Vec, did) {
                let mut rng = rand::rng();
                let len = rng.random_range(2..=5);
                let mut elements = Vec::new();
                for _ in 0..len {
                    let element_ty = args.type_at(0);
                    let element_input = self.gen(element_ty, tcx, resolver);
                    elements.push(element_input);
                }
                return Some(format!("vec![{}]", elements.join(", ")));
            }
        }
        None
    }

    fn gen_with_hint<'tcx>(
        &mut self,
        ty: Ty<'tcx>,
        hint: Option<&InputHint>,
        tcx: TyCtxt<'tcx>,
        resolver: &PathResolver<'tcx>,
    ) -> String {
        if let Some(hint) = hint {
            match &hint.kind {
                InputHintKind::NullPtr => {
                    if let TyKind::RawPtr(inner_ty, mutability) = ty.kind() {
                        return null_ptr_expr(*inner_ty, *mutability, resolver);
                    }
                }
                InputHintKind::DanglingPtr => {
                    if let TyKind::RawPtr(inner_ty, mutability) = ty.kind() {
                        return raw_ptr_cast_expr(1, *inner_ty, *mutability, resolver);
                    }
                }
                InputHintKind::MisalignedPtr | InputHintKind::InvalidAlign => {
                    if let TyKind::RawPtr(inner_ty, mutability) = ty.kind() {
                        return raw_ptr_cast_expr(3, *inner_ty, *mutability, resolver);
                    }
                }
                InputHintKind::UninitValue => {
                    if let TyKind::Adt(adt_def, args) = ty.kind() {
                        if is_maybe_uninit(tcx, *adt_def) {
                            let inner_ty = args.type_at(0);
                            return format!(
                                "std::mem::MaybeUninit::<{}>::uninit()",
                                resolver.ty_str(inner_ty)
                            );
                        }
                    }
                }
                InputHintKind::InvalidUtf8 => {
                    if let Some(expr) = hinted_bytes_expr(ty, &[0xff, 0xfe], tcx, resolver) {
                        return expr;
                    }
                }
                InputHintKind::InvalidCStr => match ty.kind() {
                    TyKind::RawPtr(inner_ty, mutability) => {
                        return cstr_raw_ptr_expr(*inner_ty, *mutability, resolver);
                    }
                    _ => {
                        if let Some(expr) = hinted_bytes_expr(ty, b"unterminated", tcx, resolver) {
                            return expr;
                        }
                    }
                },
                InputHintKind::NoneVariant => {
                    if let TyKind::Adt(adt_def, args) = ty.kind() {
                        if tcx.is_diagnostic_item(sym::Option, adt_def.did()) {
                            return format!("None::<{}>", resolver.ty_str(args.type_at(0)));
                        }
                    }
                }
                InputHintKind::ErrVariant => {
                    if let TyKind::Adt(adt_def, args) = ty.kind() {
                        if tcx.is_diagnostic_item(sym::Result, adt_def.did()) {
                            let ok_ty = args.type_at(0);
                            let err_ty = args.type_at(1);
                            let err_expr = self.gen(err_ty, tcx, resolver);
                            return format!(
                                "Err::<{}, {}>({})",
                                resolver.ty_str(ok_ty),
                                resolver.ty_str(err_ty),
                                err_expr
                            );
                        }
                    }
                }
                InputHintKind::OverlappingRange => {
                    if let TyKind::Adt(adt_def, args) = ty.kind() {
                        if is_range(tcx, *adt_def) {
                            if let Some(expr) = zero_one_range_for_ty(args.type_at(0)) {
                                return expr;
                            }
                        }
                    }
                }
                InputHintKind::InvalidIndex | InputHintKind::Numeric(_) => {}
            }

            match ty.kind() {
                TyKind::Int(int_ty) => {
                    if let Some(value) = hint.gen_int(*int_ty, &mut self.rng) {
                        return value;
                    }
                }
                TyKind::Uint(uint_ty) => {
                    if let Some(value) = hint.gen_uint(*uint_ty, &mut self.rng) {
                        return value;
                    }
                }
                _ => {}
            }
        }
        self.gen(ty, tcx, resolver)
    }

    fn gen_adt<'tcx>(
        &mut self,
        adt_def: AdtDef<'tcx>,
        args: GenericArgsRef<'tcx>,
        tcx: TyCtxt<'tcx>,
        resolver: &PathResolver<'tcx>,
    ) -> String {
        let name = resolver.path_str_with_args(adt_def.did(), args);
        if adt_def.is_struct() {
            // generate input for each field
            let mut fields = Vec::new();
            for field in adt_def.all_fields() {
                let field_name = field.name.to_string();
                let field_type = field.ty(tcx, args);
                let field_input = self.gen(field_type, tcx, resolver).to_string();
                fields.push(format!("{field_name}: {field_input}"));
            }
            return format!("{name} {{ {} }}", fields.join(", "));
        }
        if adt_def.is_enum() {
            let mut fields = Vec::new();

            let variants = adt_def.variants().into_iter().collect::<Vec<_>>();
            let variant_def = variants.choose(&mut self.rng).unwrap();
            let variant_name = variant_def.name.to_string();

            for field in variant_def.fields.iter() {
                let field_name = field.name.to_string();
                let field_type = field.ty(tcx, args);
                let field_input = self.gen(field_type, tcx, resolver).to_string();
                fields.push(format!("{field_name}: {field_input}"));
            }
            if fields.is_empty() {
                return format!("{name}::{variant_name}");
            }
            return format!("{name}::{variant_name} {{ {} }}", fields.join(", "));
        }
        panic!("Unsupported ADT ({:?},{:?})", adt_def, args)
    }
}
