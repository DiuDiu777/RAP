use std::{mem, slice};

pub struct TypedWindow {
    buf: Vec<u8>,
    offset: usize,
    count: usize,
}

impl TypedWindow {
    pub fn new(len: usize) -> Self {
        Self {
            buf: vec![0; len.max(1)],
            offset: 0,
            count: 0,
        }
    }

    pub fn select_offset(&mut self, offset: usize) {
        self.offset = offset.min(self.buf.len() - 1);
        self.count = 0;
    }

    pub fn set_count<T>(&mut self, count: usize) {
        let width = mem::size_of::<T>().max(1);
        let remain = self.buf.len().saturating_sub(self.offset);
        self.count = count.min(remain / width);
    }

    pub fn view<T>(&self) -> &[T] {
        assert!(self.count > 0);
        let width = mem::size_of::<T>().max(1);
        let needed = self.count.checked_mul(width).unwrap();
        assert!(self.offset + needed <= self.buf.len());

        unsafe {
            let ptr = self.buf.as_ptr().add(self.offset) as *const T;
            slice::from_raw_parts(ptr, self.count)
        }
    }
}
