#![allow(unused)]

enum Selector {
    First,
    Second,
}

// Expected alias analysis result: (0, 1) (0, 2)
fn foo(x: *mut i32, y: *mut i32, choice: Selector) -> *mut i32 {
    let mut r = x;

    unsafe {
        while *r > 0 {
            let mut p = match choice {
                Selector::First => y,
                Selector::Second => x,
            };

            loop {
                let q = match choice {
                    Selector::First => x,
                    Selector::Second => p,
                };
                *q -= 1;
                if *r <= 1 {
                    break;
                }
                p = y;
                r = q;
            }

            if *r == 0 {
                break;
            }
        }
    }

    r
}
