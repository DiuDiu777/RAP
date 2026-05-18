pub struct OptionBox {
    pub value: Option<i32>,
}

impl OptionBox {
    pub fn new(value: Option<i32>) -> Self {
        Self { value }
    }

    pub fn get(&self) -> i32 {
        unsafe { self.value.unwrap_unchecked() }
    }
}
