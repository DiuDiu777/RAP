pub struct ReadBox {
    pub ptr: *const i32,
}

impl ReadBox {
    pub fn new(value: &i32) -> Self {
        Self {
            ptr: value as *const i32,
        }
    }

    pub fn read(&self) -> i32 {
        unsafe { core::ptr::read(self.ptr) }
    }
}
