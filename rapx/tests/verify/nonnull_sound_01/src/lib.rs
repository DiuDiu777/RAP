#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn callee_require_nonnull(_ptr: *const u32) {}

// An unsafe caller whose own contract declares ptr as NonNull.
// Used as a callee for contract propagation test.
#[rapx::requires(NonNull(ptr), kind = "precond")]
unsafe fn caller_with_contract(ptr: *const u32) {}

// SOUND: the caller's `#[rapx::requires(NonNull(ptr))]` is injected
// as a ContractFact at function entry, establishing NonNull(ptr)
// before the call, satisfying callee's NonNull requirement.
#[rapx::requires(NonNull(ptr), kind = "precond")]
#[rapx::verify]
pub unsafe fn sound_caller_contract_propagates_to_callee(ptr: *const u32) {
    unsafe {
        callee_require_nonnull(ptr);
    }
}

// SOUND: chained unsafe callers — inner caller's contract propagates.
#[rapx::requires(NonNull(ptr), kind = "precond")]
#[rapx::verify]
pub unsafe fn sound_chained_propagation(ptr: *const u32) {
    unsafe {
        caller_with_contract(ptr);
    }
}
