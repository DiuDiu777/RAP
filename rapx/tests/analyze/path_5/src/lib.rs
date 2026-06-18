#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused)]

// Nested SCC: inner retry loop inside outer retry loop.
#[rapx::verify]
fn read2(x: bool) -> Option<u32> {
    let mut outer_retry = true;

    loop {
        let mut inner_retry = true;

        loop {
            if x {
                return Some(42);
            } else if inner_retry {
                inner_retry = false;
                continue;
            } else {
                break;
            }
        }

        if outer_retry {
            outer_retry = false;
            continue;
        }

        return None;
    }
}
