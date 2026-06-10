pub struct SliceView {
    ptr: *const u64,
    len: usize,
}

impl SliceView {
    pub fn new(data: &[u64]) -> Self {
        Self {
            ptr: data.as_ptr(),
            len: data.len(),
        }
    }

    pub fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    pub fn as_slice(&self) -> &[u64] {
        unsafe { core::slice::from_raw_parts(self.ptr, self.len) }
    }
}
