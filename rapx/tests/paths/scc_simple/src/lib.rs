// Single loop (SCC) with conditional branch inside.
// Tests that PathEnumerator correctly decomposes the SCC and
// produces finite, distinct paths through the loop body.

fn classify(x: i32) -> i32 {
    let mut i = 0;
    loop {
        if i >= x {
            break;
        }
        if i % 2 == 0 {
            i += 1;
        } else {
            i += 2;
        }
    }
    i
}

fn early_exit(x: i32) -> i32 {
    let mut i = 0;
    loop {
        if i >= x {
            return i;
        }
        i += 1;
    }
}
