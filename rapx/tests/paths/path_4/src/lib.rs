#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused)]

// SCC with alignment check + retry loop.
#[rapx::verify]
fn read1<T>(ptr: *const T) -> Option<u32> {
    let mut retry = true;

    loop {
        let p = if (ptr as usize) % std::mem::align_of::<u32>() == 0 {
            ptr as *const u32
        } else if retry {
            retry = false;
            continue;
        } else {
            return None;
        };

        let v = unsafe { p.read() };
        return Some(v);
    }
}
