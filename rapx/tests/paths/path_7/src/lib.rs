#![allow(dead_code)]

// SCC with early return from inside the loop.
fn early_exit(x: i32) -> i32 {
    let mut i = 0;
    loop {
        if i >= x {
            return i;
        }
        i += 1;
    }
}
