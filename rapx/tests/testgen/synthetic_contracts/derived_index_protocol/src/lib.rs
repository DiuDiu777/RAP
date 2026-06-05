pub struct PagedTable {
    data: Vec<i32>,
    page_size: usize,
    page: usize,
    slot: usize,
    idx: usize,
}

impl PagedTable {
    pub fn new(data: Vec<i32>, page_size: usize) -> Self {
        Self {
            data,
            page_size: page_size.max(1),
            page: 0,
            slot: 0,
            idx: 0,
        }
    }

    pub fn select_page(&mut self, page: usize) {
        self.page = page;
    }

    pub fn select_slot(&mut self, slot: usize) {
        self.slot = slot.min(self.page_size - 1);
    }

    pub fn commit(&mut self) {
        self.idx = self
            .page
            .saturating_mul(self.page_size)
            .saturating_add(self.slot);
    }

    pub fn get(&self) -> &i32 {
        unsafe { self.data.get_unchecked(self.idx) }
    }
}
