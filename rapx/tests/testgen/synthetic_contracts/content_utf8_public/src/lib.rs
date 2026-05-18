pub struct Utf8Box {
    pub bytes: Vec<u8>,
}

impl Utf8Box {
    pub fn new(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }

    pub fn into_string(self) -> String {
        unsafe { String::from_utf8_unchecked(self.bytes) }
    }
}
