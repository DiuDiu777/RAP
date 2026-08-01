#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

use std::marker::PhantomData;

#[rapx::invariant(any(Null(prev), (Align(prev, Node), ValidPtr(prev, Node, 1), Allocated(prev, Node, 1), Typed(prev, Node), Owning(prev))))]
#[rapx::invariant(any(Null(next), (Align(next, Node), ValidPtr(next, Node, 1), Allocated(next, Node, 1), Typed(next, Node), Owning(next))))]
struct Node<T> {
    value: T,
    prev: *mut Node<T>,
    next: *mut Node<T>,
}

#[rapx::invariant(any(Null(head), (Align(head, Node), ValidPtr(head, Node, 1), Allocated(head, Node, 1), Typed(head, Node), Owning(head))))]
#[rapx::invariant(any(Null(tail), (Align(tail, Node), ValidPtr(tail, Node, 1), Allocated(tail, Node, 1), Typed(tail, Node), Owning(tail))))]
struct LinkedList<T> {
    head: *mut Node<T>,
    tail: *mut Node<T>,
    len: usize,
    _marker: PhantomData<Box<Node<T>>>,
}

impl<T> LinkedList<T> {
    #[rapx::verify]
    pub fn new() -> Self {
        LinkedList {
            head: std::ptr::null_mut(),
            tail: std::ptr::null_mut(),
            len: 0,
            _marker: PhantomData,
        }
    }

    #[rapx::verify]
    pub fn len(&self) -> usize {
        self.len
    }

    #[rapx::verify]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[rapx::verify]
    pub fn push_back(&mut self, value: T) {
        let node = Box::into_raw(Box::new(Node {
            value,
            prev: self.tail,
            next: std::ptr::null_mut(),
        }));
        unsafe {
            if self.tail.is_null() {
                self.head = node;
                self.tail = node;
            } else {
                (*self.tail).next = node;
                self.tail = node;
            }
        }
        self.len += 1;
    }

    #[rapx::verify]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.head.is_null() {
            return None;
        }
        let old_head = self.head;
        let boxed = unsafe { Box::from_raw(old_head) };
        let Node { value, next, .. } = *boxed;
        self.head = next;
        if self.head.is_null() {
            self.tail = std::ptr::null_mut();
        } else {
            unsafe {
                (*self.head).prev = std::ptr::null_mut();
            }
        }
        self.len -= 1;
        Some(value)
    }

    #[rapx::verify]
    pub fn pop_back(&mut self) -> Option<T> {
        if self.tail.is_null() {
            return None;
        }
        let old_tail = self.tail;
        let boxed = unsafe { Box::from_raw(old_tail) };
        let Node { value, prev, .. } = *boxed;
        self.tail = prev;
        if self.tail.is_null() {
            self.head = std::ptr::null_mut();
        } else {
            unsafe {
                (*self.tail).next = std::ptr::null_mut();
            }
        }
        self.len -= 1;
        Some(value)
    }

    #[rapx::verify]
    pub fn clear(&mut self) {
        let mut current = self.head;
        unsafe {
            while !current.is_null() {
                let next = (*current).next;
                drop(Box::from_raw(current));
                current = next;
            }
        }
        self.head = std::ptr::null_mut();
        self.tail = std::ptr::null_mut();
        self.len = 0;
    }

    #[rapx::verify]
    pub fn from_vec(values: Vec<T>) -> Self {
        let mut list = Self::new();
        for value in values {
            list.push_back(value);
        }
        list
    }
}

impl<T: Copy> LinkedList<T> {
    // SOUND under T: Copy — ptr::read of a Copy type is safe because
    // the value is duplicated bitwise and no double-drop can occur.
    #[rapx::verify]
    pub fn front_copy(&self) -> Option<T> {
        if self.head.is_null() {
            None
        } else {
            unsafe { Some(std::ptr::read(&(*self.head).value)) }
        }
    }

    #[rapx::verify]
    pub fn back_copy(&self) -> Option<T> {
        if self.tail.is_null() {
            None
        } else {
            unsafe { Some(std::ptr::read(&(*self.tail).value)) }
        }
    }

    // With T: Copy, returning &mut T from a raw pointer is still UB
    // due to Rust's aliasing rules.  Use ptr::read to return by value
    // instead, which is safe for Copy types.
    #[rapx::verify]
    pub fn front_mut_copy(&mut self) -> Option<T> {
        if self.head.is_null() {
            None
        } else {
            unsafe { Some(std::ptr::read(&(*self.head).value)) }
        }
    }

    #[rapx::verify]
    pub fn back_mut_copy(&mut self) -> Option<T> {
        if self.tail.is_null() {
            None
        } else {
            unsafe { Some(std::ptr::read(&(*self.tail).value)) }
        }
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        let mut current = self.head;
        unsafe {
            while !current.is_null() {
                let next = (*current).next;
                drop(Box::from_raw(current));
                current = next;
            }
        }
    }
}
