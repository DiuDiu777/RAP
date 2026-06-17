use std::slice;

// 1. Dataflow: p => ret value.
fn get_new_vec(p: &[u8]) -> Vec<u8> {
    p.iter().map(|x| x + 1).collect()
}

// 2. Dataflow: v => ret value.
// 3. Alias: (v, ret value)
unsafe fn get_vec(v: &mut [u8]) -> Vec<u8> {
    let ptr = v.as_mut_ptr();
    let len = v.len();
    unsafe { Vec::from_raw_parts(ptr, len, len) }
}

// 7. Is the interior unsafe function sound?
fn get_slice<T>(s: &[T], l: usize) -> &[u32] {
    let ptr = s.as_ptr() as *const u32;
    let len = s.len();
    if l < len {
        // 8. Path constraint: l < len;
        // 9. The safe condition should be l*4 < len + 1 => possible out-of-bound access;
        unsafe { slice::from_raw_parts(ptr, l) }
    } else {
        unsafe { slice::from_raw_parts(ptr, len) }
    }
}

fn main() {
    let mut v1 = vec![1; 10];

    // 4. v1 and v2 are aliases, so the value has two owners => double free
    let _v2 = unsafe { get_vec(&mut v1) };

    // 5. v3 is not an alias of v1, and it is a new value.
    let v3 = get_new_vec(&v1);

    // 10. trigger out-of-bound access.
    let _ = get_slice(&v3, 5);

    // 6. vec3 is a heap owner, into_raw_parts() consumes the ownership  => memory leakage.
    let _ = v3.into_raw_parts();
}
