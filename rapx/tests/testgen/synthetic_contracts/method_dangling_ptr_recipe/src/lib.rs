use std::ptr;

pub struct PtrSlot {
    ptr: *const i32,
}

impl PtrSlot {
    pub fn new() -> Self {
        Self { ptr: ptr::null() }
    }

    pub fn set_ptr(&mut self, ptr: *const i32) {
        self.ptr = ptr;
    }

    pub fn read(&self) -> i32 {
        assert!(!self.ptr.is_null());
        unsafe { ptr::read(self.ptr) }
    }
}

impl Default for PtrSlot {
    fn default() -> Self {
        Self::new()
    }
}
