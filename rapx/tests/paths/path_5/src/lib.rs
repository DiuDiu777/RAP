#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused)]

// Nested SCC: inner retry loop inside outer retry loop.
#[rapx::verify]
fn read2<T>(ptr: *const T) -> Option<u32> {
    let mut outer_retry = true;

    loop {
        let mut inner_retry = true;

        loop {
            let p = if (ptr as usize) % std::mem::align_of::<u32>() == 0 {
                ptr as *const u32
            } else if inner_retry {
                inner_retry = false;
                continue;
            } else {
                break;
            };

            let v = unsafe { p.read() };
            return Some(v);
        }

        if outer_retry {
            outer_retry = false;
            continue;
        }

        return None;
    }
}
