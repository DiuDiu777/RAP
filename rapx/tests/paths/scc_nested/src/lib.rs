// Nested loops (nested SCCs) with controlled repetition.
// Tests that PathEnumerator correctly enumerates child SCC paths
// as atomic building blocks within the parent SCC.

fn walk(rows: i32, cols: i32) -> i32 {
    let mut total = 0;
    let mut r = 0;
    loop {
        if r >= rows {
            break;
        }
        let mut c = 0;
        loop {
            if c >= cols {
                break;
            }
            total += 1;
            c += 1;
        }
        r += 1;
    }
    total
}

fn double_loop(x: i32) -> i32 {
    let mut i = 0;
    loop {
        if i >= x {
            break;
        }
        let mut j = 0;
        loop {
            if j >= x {
                break;
            }
            j += 1;
        }
        i += 1;
    }
    i
}
