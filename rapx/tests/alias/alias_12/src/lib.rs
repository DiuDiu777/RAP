#[derive(Debug)]
#[allow(dead_code)]
struct Leaf {
    value: Box<i32>,
}

#[derive(Debug)]
#[allow(dead_code)]
struct Node {
    leaf1: Box<Leaf>,
    leaf2: Box<Leaf>,
    weight: i32,
}

#[derive(Debug)]
#[allow(dead_code)]
struct Middle {
    node1: Box<Node>,
    node2: Box<Node>,
    leaf: Box<Leaf>,
    bias: i32,
}

#[derive(Debug)]
#[allow(dead_code)]
struct Root {
    middle: Box<Middle>,
    offset: i32,
}

#[allow(dead_code)]
fn foo(c: usize, root: &Root) -> &Leaf {
    if c == 0 {
        &root.middle.leaf
    } else {
        &root.middle.node2.leaf2
    }
}
