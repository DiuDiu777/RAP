#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused)]

fn example(x: Option<i32>) -> i32 {
    let a = match x {
        Some(_) => 1,
        None => -1,
    };
    match x {
        Some(_) => a + 1,
        None => a - 1,
    }
}
