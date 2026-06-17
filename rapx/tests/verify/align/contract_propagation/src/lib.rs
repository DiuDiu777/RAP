#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn callee_require_nonnull(_ptr: *const u32) {}

// SOUND: The caller's contract NonNull(ptr) should propagate to
// the callee call site, satisfying callee's NonNull requirement.
#[rapx::requires(NonNull(ptr), kind = "precond")]
#[rapx::verify]
unsafe fn caller_propagates_nonnull(ptr: *const u32) {
    unsafe {
        callee_require_nonnull(ptr);
    }
}
