pub struct IndexBox {
    pub data: Vec<i32>,
    pub idx: usize,
}

impl IndexBox {
    pub fn new(data: Vec<i32>) -> Self {
        Self { data, idx: 0 }
    }

    pub fn get(&self) -> &i32 {
        unsafe { self.data.get_unchecked(self.idx) }
    }
}
