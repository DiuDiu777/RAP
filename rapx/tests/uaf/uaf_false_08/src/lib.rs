#[allow(dead_code)]
struct S {
    field: String,
}

#[allow(dead_code)]
impl S {
    fn mutate(&mut self, s: String) {
        self.field = s;
    }
}
