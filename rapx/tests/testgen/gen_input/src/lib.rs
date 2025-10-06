pub fn gen_static_str(s: &'static str) {}
pub fn gen_str_ref(s: &str) {}
pub fn gen_slice(s: &[i32]) {}
pub fn gen_ref_slice(s: &mut [String]) {}
pub fn gen_tuple(t: (i32, String, &str, &[i32])) {}

#[non_exhaustive]
pub enum MyList {
    A,
}

pub fn gen_mylist(l: MyList) {}
