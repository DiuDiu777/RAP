pub struct PtrReadBox {
    pub ptr: *const String,
}

impl PtrReadBox {
    pub fn new(value: &String) -> Self {
        Self {
            ptr: value as *const String,
        }
    }

    pub fn duplicate(&self) -> String {
        unsafe { core::ptr::read(self.ptr) }
    }
}
