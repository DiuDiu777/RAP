use std::ptr;

pub struct ExposedLenVec {
    data: Vec<u32>,
    initialized: usize,
}

impl ExposedLenVec {
    pub fn new(cap: usize, init: usize, seed: u32) -> Self {
        let cap = cap.max(1);
        let initialized = init.min(cap);
        let mut data = Vec::with_capacity(cap);
        for i in 0..initialized {
            data.push(seed.wrapping_add(i as u32));
        }
        Self { data, initialized }
    }

    pub fn expose_len(&mut self, len: usize) {
        let len = len.min(self.data.capacity());
        unsafe {
            self.data.set_len(len);
        }
    }

    pub fn initialized_len(&self) -> usize {
        self.initialized
    }

    pub fn read_at(&self, idx: usize) -> u32 {
        assert!(idx < self.data.len());
        unsafe { ptr::read(self.data.as_ptr().add(idx)) }
    }
}
