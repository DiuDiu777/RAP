#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused)]

// Branch-based paths: ManuallyDrop branch produces cleanup block.
#[rapx::verify]
fn read2<T>(ptr: *const T) -> Option<u32> {
    let p: *const u32;
    if (ptr as usize) % std::mem::align_of::<u32>() == 0 {
        p = ptr as *const u32;
    } else {
        let mut b = std::mem::ManuallyDrop::new(vec![0u8; std::mem::size_of::<u32>()]);
        p = b.as_ptr() as *const u32;
    }
    let value = unsafe { p.read() };
    Some(value)
}
