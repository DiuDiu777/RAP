use std::ptr::NonNull;

pub struct NonNullBox {
    pub ptr: *mut i32,
}

impl NonNullBox {
    pub fn new(value: &mut i32) -> Self {
        Self {
            ptr: value as *mut i32,
        }
    }

    pub fn non_null(&self) -> NonNull<i32> {
        unsafe { NonNull::new_unchecked(self.ptr) }
    }
}
