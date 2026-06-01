#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused)]

use std::mem::ManuallyDrop;

// Target unsafe callsite: p.read()
// One path should be generated for verification.
#[rapx::verify]
fn read1<T>(ptr: *const T) -> Option<u32> {
    let p: Option<*const u32> = if (ptr as usize) % std::mem::align_of::<u32>() == 0 {
        Some(ptr as *const u32)
    } else {
        None
    };

    let p = match p {
        Some(p) => p,
        None => return None,
    };

    unsafe { Some(p.read()) }
}

// Target unsafe callsite: p.read()
// Two paths should be generated for verification 
#[rapx::verify]
fn read2<T>(ptr: *const T) -> Option<u32> {
    let p: *const u32;

    if (ptr as usize) % std::mem::align_of::<u32>() == 0 {
        p = ptr as *const u32;
    } else {
        let mut b = ManuallyDrop::new(vec![0u8; std::mem::size_of::<u32>()]);
        p = b.as_ptr() as *const u32;
    }

    let value = unsafe { p.read() };
    Some(value)
}
