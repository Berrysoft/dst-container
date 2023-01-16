use std::{
    alloc::{AllocError, Allocator, Global, Layout},
    ptr::{NonNull, Pointee},
};

struct FixedAlloc<T: ?Sized> {
    alloc: Global,
    metadata: <T as Pointee>::Metadata,
}

impl<T: ?Sized> FixedAlloc<T> {
    pub fn new(metadata: <T as Pointee>::Metadata) -> Self {
        Self {
            alloc: Global,
            metadata,
        }
    }

    unsafe fn layout(&self) -> Layout {
        Layout::for_value_raw(std::ptr::from_raw_parts::<T>(
            std::ptr::null(),
            self.metadata,
        ))
    }

    unsafe fn align_layout(&self, layout: Layout) -> Layout {
        let single_layout = self.layout();
        let layout = Layout::from_size_align_unchecked(
            layout.size(),
            layout.align().max(single_layout.align()),
        );
        layout.pad_to_align()
    }
}

unsafe impl<T: ?Sized> Allocator for FixedAlloc<T> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let layout = unsafe { self.align_layout(layout) };
        self.alloc.allocate(layout)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let layout = self.align_layout(layout);
        self.alloc.deallocate(ptr, layout)
    }
}

pub struct FixedVec<T: ?Sized> {
    buffer: Vec<u8, FixedAlloc<T>>,
}

impl<T: ?Sized> FixedVec<T> {
    pub fn new(metadata: <T as Pointee>::Metadata) -> Self {
        Self {
            buffer: Vec::new_in(FixedAlloc::new(metadata)),
        }
    }
}
