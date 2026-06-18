#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused)]

// SCC with condition + retry loop.
#[rapx::verify]
fn read1(x: bool) -> Option<u32> {
    let mut retry = true;

    loop {
        if x {
            return Some(42);
        } else if retry {
            retry = false;
            continue;
        } else {
            return None;
        }
    }
}
