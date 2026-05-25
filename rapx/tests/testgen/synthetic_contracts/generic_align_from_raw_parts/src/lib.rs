use core::marker::PhantomData;

pub struct MutableBuffer {
    pub data: Vec<i32>,
}

impl MutableBuffer {
    pub fn from_i32_vec(data: Vec<i32>) -> Self {
        Self { data }
    }
}

impl From<Vec<i32>> for MutableBuffer {
    fn from(data: Vec<i32>) -> Self {
        Self::from_i32_vec(data)
    }
}

pub struct BufferBuilder<T> {
    pub buffer: MutableBuffer,
    pub len: usize,
    _marker: PhantomData<T>,
}

impl<T> BufferBuilder<T> {
    pub fn new_from_buffer(buffer: MutableBuffer) -> Self {
        Self {
            buffer,
            len: 1,
            _marker: PhantomData,
        }
    }

    pub fn as_slice(&self) -> &[T] {
        let ptr = self.buffer.data.as_ptr() as *const T;
        unsafe { core::slice::from_raw_parts(ptr, self.len) }
    }
}
