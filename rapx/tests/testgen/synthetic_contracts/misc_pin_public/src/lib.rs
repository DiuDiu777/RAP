use std::pin::Pin;

pub struct PinBox {
    pub value: String,
}

impl PinBox {
    pub fn new(value: String) -> Self {
        Self { value }
    }

    pub fn pin_value(&mut self) -> Pin<&mut String> {
        unsafe { Pin::new_unchecked(&mut self.value) }
    }

    pub fn move_value(&mut self) -> String {
        std::mem::take(&mut self.value)
    }
}
