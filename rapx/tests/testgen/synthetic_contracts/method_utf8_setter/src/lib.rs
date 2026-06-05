pub struct Utf8Slot {
    bytes: Vec<u8>,
}

impl Utf8Slot {
    pub fn new(seed: String) -> Self {
        Self {
            bytes: seed.into_bytes(),
        }
    }

    pub fn replace_bytes(&mut self, bytes: Vec<u8>) {
        self.bytes = bytes;
    }

    pub fn as_string(&self) -> String {
        unsafe { String::from_utf8_unchecked(self.bytes.clone()) }
    }
}
