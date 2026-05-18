pub struct LayoutBox {
    pub size: usize,
    pub align: usize,
}

impl LayoutBox {
    pub fn new(size: usize, align: usize) -> Self {
        Self { size, align }
    }

    pub fn layout(&self) -> std::alloc::Layout {
        unsafe { std::alloc::Layout::from_size_align_unchecked(self.size, self.align) }
    }
}
