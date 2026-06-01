pub struct StateBox {
    data: Vec<i32>,
    pub idx: usize,
}

impl StateBox {
    pub fn new(data: Vec<i32>) -> Self {
        Self { data, idx: 0 }
    }

    pub fn set_idx(&mut self, idx: usize) {
        self.idx = idx;
    }

    pub fn get(&self) -> &i32 {
        unsafe { self.data.get_unchecked(self.idx) }
    }
}
