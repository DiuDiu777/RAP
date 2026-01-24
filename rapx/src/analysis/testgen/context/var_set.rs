use super::Var;
use bit_set::BitSet;

pub struct VarSet {
    inner: BitSet,
}

impl Default for VarSet {
    fn default() -> Self {
        VarSet::new()
    }
}

// pub struct Iter<T: Iterator<Item = usize>> {
//     inner: T,
// }

// impl<T> Iterator for Iter<T>
// where
//     T: Iterator<Item = usize>,
// {
//     type Item = Var;
//     fn next(&mut self) -> Option<Self::Item> {
//         self.inner.next().map(Var)
//     }
// }

impl VarSet {
    pub fn new() -> Self {
        VarSet {
            inner: BitSet::new(),
        }
    }

    pub fn insert(&mut self, var: Var) -> bool {
        self.inner.insert(var.index())
    }

    pub fn contains(&self, var: Var) -> bool {
        self.inner.contains(var.index())
    }

    pub fn remove(&mut self, var: Var) -> bool {
        self.inner.remove(var.index())
    }

    pub fn iter(&self) -> impl Iterator + '_ {
        self.inner.iter()
    }
}
