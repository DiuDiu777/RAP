pub struct MutRefBox {
    pub ptr: *mut i32,
}

impl MutRefBox {
    pub fn new(value: &mut i32) -> Self {
        Self {
            ptr: value as *mut i32,
        }
    }

    pub fn get_mut<'a>(&self) -> &'a mut i32 {
        unsafe { self.ptr.as_mut().unwrap_unchecked() }
    }
}
