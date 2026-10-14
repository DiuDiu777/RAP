#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused)]

use std::ptr::NonNull;

#[rapx::invariant(Allocated(ptr, u8, capacity))]
#[rapx::invariant(Align(ptr, usize))]
#[rapx::invariant(Owning(ptr))]
#[rapx::invariant(Alias(ptr))]
#[rapx::invariant(InBound(ptr, u8, capacity))]
pub struct BumpAllocator {
    ptr: NonNull<u8>,
    capacity: usize,
    offset: usize,
}

impl BumpAllocator {
    #[rapx::verify]
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0);

        // Align the backing buffer to `usize` so a `T`-aligned pointer can be
        // carved out for any `T` with `align_of::<T>() <= align_of::<usize>()`.
        // Allocating `capacity` `usize` elements over-provisions `capacity * 8`
        // bytes (>= `capacity`), which keeps the `Allocated(ptr, u8, capacity)`
        // invariant provable without introducing a non-linear `div_ceil`.
        let mut buf: Vec<usize> = vec![0; capacity];
        let ptr = NonNull::new(buf.as_mut_ptr() as *mut u8).expect("non-null after vec alloc");

        std::mem::forget(buf);

        Self {
            ptr,
            capacity,
            offset: 0,
        }
    }

    #[rapx::verify]
    pub fn alloc(&mut self, value: u64) -> *mut u64 {
        let align = std::mem::align_of::<u64>();
        let size = std::mem::size_of::<u64>();

        // A bump allocator rounds up to `align`, but its backing buffer is only
        // `usize`-aligned; reject over-aligned types up front.
        assert!(align <= std::mem::align_of::<usize>());

        let start = (self.offset + align - 1) & !(align - 1);

        assert!(start + size <= self.capacity);

        assert!(start % align == 0);

        let p = unsafe { self.ptr.as_ptr().add(start) as *mut u64 };

        unsafe {
            p.write(value);
        }

        self.offset = start + size;

        p
    }

    #[rapx::verify]
    pub fn reset(&mut self) {
        self.offset = 0;
    }
}

impl Drop for BumpAllocator {
    fn drop(&mut self) {
        unsafe {
            drop(Vec::from_raw_parts(
                self.ptr.as_ptr(),
                self.capacity,
                self.capacity,
            ));
        }
    }
}
