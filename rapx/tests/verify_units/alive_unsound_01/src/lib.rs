#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::marker::PhantomData;

#[rapx::invariant(NonNull(ptr))]
#[rapx::invariant(ValidPtr(ptr, T, len))]
#[rapx::invariant(Init(ptr, T, len))]
pub struct DangerousAliaser<'a, T> {
    ptr: *mut T,
    len: usize,
    _marker: PhantomData<&'a mut [T]>,
}

impl<'a, T> DangerousAliaser<'a, T> {
    #[rapx::verify]
    pub fn new(data: &'a mut [T]) -> Self {
        Self {
            ptr: data.as_mut_ptr(),
            len: data.len(),
            _marker: PhantomData,
        }
    }

    // UNSOUND: `&self` has no lifetime binding — its anonymous borrow
    // lifetime is independent of struct param `'a`.  The struct's `'a`
    // only binds the struct itself and its fields together, not `&self`.
    // Therefore `Alive(ptr, 'a')` cannot be proved: `'a` is unbounded at
    // the call site, and the verifier cannot guarantee the allocation
    // outlives an unconstrained lifetime.
    #[rapx::verify]
    pub fn get_mut(&mut self) -> &'a mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}
