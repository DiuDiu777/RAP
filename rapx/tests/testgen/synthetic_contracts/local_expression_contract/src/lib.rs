pub struct ManualExprBox {
    data: Vec<u8>,
    len: usize,
}

#[inline(never)]
unsafe fn raw_len_sink(ptr: *const u8, len: usize) -> u8 {
    *ptr.add(len.wrapping_sub(1))
}

impl ManualExprBox {
    pub fn new(seed: u8) -> Self {
        Self {
            data: vec![seed],
            len: 1,
        }
    }

    pub fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    pub fn read_tail(&self) -> u8 {
        unsafe { raw_len_sink(self.data.as_ptr(), self.len) }
    }
}
