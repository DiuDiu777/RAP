use std::ffi::CStr;

pub struct CStrBox {
    pub bytes: Vec<u8>,
}

impl CStrBox {
    pub fn new(bytes: Vec<u8>) -> Self {
        Self { bytes }
    }

    pub fn as_cstr(&self) -> &CStr {
        unsafe { CStr::from_bytes_with_nul_unchecked(&self.bytes) }
    }
}
