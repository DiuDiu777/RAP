pub struct AlignBox {
    pub ptr: *const u32,
}

impl AlignBox {
    pub fn new(value: &u32) -> Self {
        Self {
            ptr: value as *const u32,
        }
    }

    pub fn read(&self) -> u32 {
        unsafe { core::ptr::read(self.ptr) }
    }
}
