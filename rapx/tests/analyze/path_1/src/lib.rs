#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused)]

#[rapx::verify]
fn read1(x: i32) -> Option<i32> {
    let p: Option<i32> = if x > 0 { Some(x) } else { None };
    match p {
        Some(v) => Some(v * 2),
        None => None,
    }
}
