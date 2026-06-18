#![allow(dead_code)]

// Nested SCC: outer row loop + inner column loop (grid walk).
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
