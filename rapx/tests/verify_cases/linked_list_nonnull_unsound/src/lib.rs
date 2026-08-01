#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

use std::ptr::NonNull;
use std::marker::PhantomData;

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
    _marker: PhantomData<Box<Node<T>>>,
}

impl<T> LinkedList<T> {
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
            let v = std::ptr::read(&r.value);
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
            let v = std::ptr::read(&r.value);
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
    pub fn front(&self) -> Option<T> {
        match self.head {
            Some(node) => unsafe {
                Some(std::ptr::read(&node.as_ref().value))
            },
            None => None,
        }
    }

    #[rapx::verify]
    pub fn back(&self) -> Option<T> {
        match self.tail {
            Some(node) => unsafe {
                Some(std::ptr::read(&node.as_ref().value))
            },
            None => None,
        }
    }

    #[rapx::verify]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        match self.head {
            Some(mut node) => Some(unsafe { &mut node.as_mut().value }),
            None => None,
        }
    }

    #[rapx::verify]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        match self.tail {
            Some(mut node) => Some(unsafe { &mut node.as_mut().value }),
            None => None,
        }
    }
}
