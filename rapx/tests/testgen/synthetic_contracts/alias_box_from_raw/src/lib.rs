pub struct RawBox {
    pub ptr: *mut i32,
}

impl RawBox {
    pub fn new(value: Box<i32>) -> Self {
        Self {
            ptr: Box::into_raw(value),
        }
    }

    pub fn take(&self) -> Box<i32> {
        unsafe { Box::from_raw(self.ptr) }
    }
}
