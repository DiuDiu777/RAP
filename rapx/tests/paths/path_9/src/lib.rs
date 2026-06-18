// Nested SCC: double counting loop (outer + inner).
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
