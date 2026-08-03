#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

#[rapx::verify]
pub fn sound_copy_nonoverlapping_adjacent(data: &mut [u32; 4]) {
    let src = data.as_ptr();
    let dst = unsafe { data.as_mut_ptr().add(1) };
    unsafe {
        std::ptr::copy_nonoverlapping(src, dst, 1);
    }
}
