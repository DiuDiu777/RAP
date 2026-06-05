pub struct SharedRawCell {
    value: Box<i32>,
    ptr: *mut i32,
}

impl SharedRawCell {
    pub fn new(value: i32) -> Self {
        let mut value = Box::new(value);
        let ptr = value.as_mut() as *mut i32;
        Self { value, ptr }
    }

    pub fn borrow(&self) -> &i32 {
        unsafe { self.ptr.as_ref().unwrap() }
    }

    pub fn write_through_shared(&self, value: i32) {
        unsafe {
            *self.ptr = value;
        }
    }

    pub fn owner_value(&self) -> i32 {
        *self.value
    }
}
