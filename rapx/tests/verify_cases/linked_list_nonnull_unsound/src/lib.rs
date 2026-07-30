#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

use std::ptr::NonNull;

#[rapx::invariant(Align(prev.unwrap_some(), Node))]
#[rapx::invariant(Allocated(prev.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(prev.unwrap_some(), Node))]
#[rapx::invariant(Owning(prev.unwrap_some()))]
#[rapx::invariant(Align(next.unwrap_some(), Node))]
#[rapx::invariant(Allocated(next.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(next.unwrap_some(), Node))]
#[rapx::invariant(Owning(next.unwrap_some()))]
struct Node<T> {
    value: T,
    prev: Option<NonNull<Node<T>>>,
    next: Option<NonNull<Node<T>>>,
}

#[rapx::invariant(Align(head.unwrap_some(), Node))]
#[rapx::invariant(Allocated(head.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(head.unwrap_some(), Node))]
#[rapx::invariant(Owning(head.unwrap_some()))]
#[rapx::invariant(Align(tail.unwrap_some(), Node))]
#[rapx::invariant(Allocated(tail.unwrap_some(), Node, 1))]
#[rapx::invariant(Typed(tail.unwrap_some(), Node))]
#[rapx::invariant(Owning(tail.unwrap_some()))]
struct LinkedList<T> {
    head: Option<NonNull<Node<T>>>,
    tail: Option<NonNull<Node<T>>>,
    len: usize,
}

impl<T: Copy> LinkedList<T> {
    #[rapx::verify]
    pub fn new() -> Self { LinkedList { head: None, tail: None, len: 0 } }

    #[rapx::verify]
    pub fn len(&self) -> usize { self.len }

    #[rapx::verify]
    pub fn is_empty(&self) -> bool { self.len == 0 }

    #[rapx::verify]
    pub fn push_back(&mut self, value: T) {
        let node = Box::new(Node { value, prev: self.tail, next: None });
        let mut node = NonNull::from(Box::leak(node));
        unsafe { match self.tail { None => { self.head = Some(node); self.tail = Some(node); } Some(mut tail) => { tail.as_mut().next = Some(node); self.tail = Some(node); } } }
        self.len += 1;
    }

    #[rapx::verify]
    pub fn push_front(&mut self, value: T) {
        let node = Box::new(Node { value, prev: None, next: self.head });
        let mut node = NonNull::from(Box::leak(node));
        unsafe { match self.head { None => { self.head = Some(node); self.tail = Some(node); } Some(mut head) => { head.as_mut().prev = Some(node); self.head = Some(node); } } }
        self.len += 1;
    }

    #[rapx::verify]
    pub fn pop_front(&mut self) -> Option<T> {
        let head = match self.head { Some(h) => h, None => return None };
        let (value, next) = unsafe {
            let r = head.as_ref();
            let v = r.value;
            let n = r.next;
            if let Some(mut next_node) = n { next_node.as_mut().prev = None; }
            (v, n)
        };
        if next.is_none() { self.tail = None; }
        unsafe { drop(Box::from_raw(head.as_ptr())); }
        self.head = next;
        self.len -= 1; Some(value)
    }

    #[rapx::verify]
    pub fn pop_back(&mut self) -> Option<T> {
        let tail = match self.tail { Some(t) => t, None => return None };
        let (value, prev) = unsafe {
            let r = tail.as_ref();
            let v = r.value;
            let p = r.prev;
            if let Some(mut prev_node) = p { prev_node.as_mut().next = None; }
            (v, p)
        };
        if prev.is_none() { self.head = None; }
        self.tail = prev;
        unsafe { drop(Box::from_raw(tail.as_ptr())); }
        self.len -= 1; Some(value)
    }

    #[rapx::verify]
    pub fn front(&self) -> Option<T> { self.head.map(|node| unsafe { node.as_ref().value }) }

    #[rapx::verify]
    pub fn back(&self) -> Option<T> { self.tail.map(|node| unsafe { node.as_ref().value }) }

    #[rapx::verify]
    pub fn front_mut(&mut self) -> Option<&mut T> { match self.head { Some(mut node) => Some(unsafe { &mut node.as_mut().value }), None => None } }

    #[rapx::verify]
    pub fn back_mut(&mut self) -> Option<&mut T> { match self.tail { Some(mut node) => Some(unsafe { &mut node.as_mut().value }), None => None } }

    #[rapx::verify]
    pub fn clear(&mut self) {
        let mut current = self.head;
        unsafe { while let Some(node) = current { current = node.as_ref().next; drop(Box::from_raw(node.as_ptr())); } }
        self.head = None; self.tail = None; self.len = 0;
    }

    #[rapx::verify]
    pub fn from_vec(values: Vec<T>) -> Self { let mut list = Self::new(); for value in values { list.push_back(value); } list }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        let mut current = self.head;
        unsafe { while let Some(node) = current { current = node.as_ref().next; drop(Box::from_raw(node.as_ptr())); } }
    }
}
