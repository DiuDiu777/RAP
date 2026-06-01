pub struct OrderedIndexBox {
    data: Vec<i32>,
    pending_idx: usize,
    idx: usize,
}

impl OrderedIndexBox {
    pub fn new(data: Vec<i32>) -> Self {
        Self {
            data,
            pending_idx: 0,
            idx: 0,
        }
    }

    pub fn set_pending_idx(&mut self, pending_idx: usize) {
        self.pending_idx = pending_idx;
    }

    pub fn commit_idx(&mut self) {
        self.idx = self.pending_idx;
    }

    pub fn get(&self) -> &i32 {
        unsafe { self.data.get_unchecked(self.idx) }
    }
}
