pub struct OffsetBox {
    pub lhs: *const u32,
    pub rhs: *const u32,
}

impl OffsetBox {
    pub fn new(slice: &[u32]) -> Self {
        let lhs = slice.as_ptr();
        let rhs = unsafe { lhs.add(slice.len()) };
        Self { lhs, rhs }
    }

    pub fn distance(&self) -> isize {
        unsafe { self.rhs.offset_from(self.lhs) }
    }
}
