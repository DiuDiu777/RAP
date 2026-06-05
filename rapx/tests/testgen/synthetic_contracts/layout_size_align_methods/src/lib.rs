use std::alloc::Layout;

pub struct LayoutCell {
    size: usize,
    align: usize,
}

impl LayoutCell {
    pub fn new() -> Self {
        Self { size: 1, align: 1 }
    }

    pub fn set_size(&mut self, size: usize) {
        self.size = size;
    }

    pub fn set_align(&mut self, align: usize) {
        self.align = align;
    }

    pub fn layout(&self) -> Layout {
        unsafe { Layout::from_size_align_unchecked(self.size, self.align) }
    }
}

impl Default for LayoutCell {
    fn default() -> Self {
        Self::new()
    }
}
