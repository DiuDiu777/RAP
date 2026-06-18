#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused)]

// Branch-based paths: if-else alignment check + match return.
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
