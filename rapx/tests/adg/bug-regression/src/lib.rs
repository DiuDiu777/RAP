#![feature(allocator_api)]
// nested type
// fuzzable check should not cause stack overflow
pub struct A {
    pub a: Vec<A>,
    pub b: Vec<A>,
}

pub fn dummy(_a: A) {}

pub fn higher_order_trait<T>()
where
    for<'a> &'a T: Default,
{
}
