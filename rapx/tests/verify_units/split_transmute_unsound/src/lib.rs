#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

struct MyType(u16, u8);

// UNSOUND: generic `T, U` without `SplitTransmute` contract.
#[rapx::verify]
pub fn align_without_contract_generic<T, U>(slice: &[T]) -> (&[T], &[U], &[T]) {
    unsafe { slice.align_to::<U>() }
}

// SOUND: `align_to::<u32>` needs no `SplitTransmute` contract because
// `MyType(u16, u8)` (3 bytes, align 1) and `u32` are the same layout.
#[rapx::verify]
pub fn align_without_contract_u32(slice: &[MyType]) -> (&[MyType], &[u32], &[MyType]) {
    unsafe { slice.align_to::<u32>() }
}

// SOUND: `align_to::<u16>` needs no `SplitTransmute` contract because
// `MyType(u16, u8)` (3 bytes, align 1) and `u16` are the same layout.
#[rapx::verify]
pub fn align_without_contract_u16(slice: &[MyType]) -> (&[MyType], &[u16], &[MyType]) {
    unsafe { slice.align_to::<u16>() }
}

// SOUND: `align_to::<u8>` needs no `SplitTransmute` contract because `u8` is
// all-bit-valid and `MyType(u16, u8)` is a byte-aligned, padding-free layout.
#[rapx::verify]
pub fn align_without_contract_u8(slice: &[MyType]) -> (&[MyType], &[u8], &[MyType]) {
    unsafe { slice.align_to::<u8>() }
}

// UNSOUND: `align_to::<bool>` from `&[u8]` without `SplitTransmute`.
#[rapx::verify]
pub fn unsound_align_to_bool_from_bytes(data: &[u8]) -> usize {
    let (_, middle, _) = unsafe { data.align_to::<bool>() };
    middle.len()
}
