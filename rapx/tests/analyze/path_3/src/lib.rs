#![allow(dead_code)]

// Simplest SCC: loop with retry — continue once, then return None.
fn retry_once() -> Option<u32> {
    let mut retry = true;
    loop {
        if retry {
            retry = false;
            continue;
        } else {
            return None;
        }
    }
}
