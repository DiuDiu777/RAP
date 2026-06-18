// SCC with conditional branch inside the loop body.
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
