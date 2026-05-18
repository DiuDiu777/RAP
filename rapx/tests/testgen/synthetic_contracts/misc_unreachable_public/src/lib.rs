pub struct ReachBox {
    pub reachable: bool,
}

impl ReachBox {
    pub fn new(reachable: bool) -> Self {
        Self { reachable }
    }

    pub fn check(&self) {
        if self.reachable {
            unsafe { std::hint::unreachable_unchecked() }
        }
    }
}
