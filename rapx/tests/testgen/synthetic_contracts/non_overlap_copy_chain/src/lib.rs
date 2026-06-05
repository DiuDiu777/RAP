use std::ptr;

pub struct CopyWindow {
    buf: Vec<u8>,
    src: usize,
    dst: usize,
    count: usize,
}

impl CopyWindow {
    pub fn new(len: usize) -> Self {
        Self {
            buf: vec![1; len.max(2)],
            src: 0,
            dst: 1,
            count: 1,
        }
    }

    pub fn select_src(&mut self, src: usize) {
        self.src = src.min(self.buf.len() - 1);
    }

    pub fn select_dst(&mut self, dst: usize) {
        self.dst = dst.min(self.buf.len() - 1);
    }

    pub fn set_count(&mut self, count: usize) {
        let max_src = self.buf.len().saturating_sub(self.src);
        let max_dst = self.buf.len().saturating_sub(self.dst);
        self.count = count.min(max_src.min(max_dst));
    }

    pub fn copy(&mut self) {
        assert!(self.count > 0);
        unsafe {
            let src = self.buf.as_ptr().add(self.src);
            let dst = self.buf.as_mut_ptr().add(self.dst);
            ptr::copy_nonoverlapping(src, dst, self.count);
        }
    }

    pub fn first(&self) -> u8 {
        self.buf[0]
    }
}
