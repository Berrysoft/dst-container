use crate::*;
use std::{
    alloc::{handle_alloc_error, AllocError, Allocator, Global, Layout},
    mem::forget,
    ops::{Index, IndexMut, RangeFull},
    ptr::{drop_in_place, NonNull, Pointee},
    slice::SliceIndex,
};

struct FixedAlloc<T: ?Sized> {
    alloc: Global,
    metadata: <T as Pointee>::Metadata,
}

impl<T: ?Sized> FixedAlloc<T> {
    pub const fn new(metadata: <T as Pointee>::Metadata) -> Self {
        Self {
            alloc: Global,
            metadata,
        }
    }

    pub const fn metadata(&self) -> <T as Pointee>::Metadata {
        self.metadata
    }

    pub unsafe fn layout(&self) -> Layout {
        Layout::for_value_raw(std::ptr::from_raw_parts::<T>(
            std::ptr::null(),
            self.metadata,
        ))
    }

    pub unsafe fn align_layout(&self, layout: Layout) -> Layout {
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

pub struct FixedVec<T: ?Sized>(Vec<u8, FixedAlloc<T>>);

impl<T: ?Sized> FixedVec<T> {
    pub const fn new(metadata: <T as Pointee>::Metadata) -> Self {
        Self(Vec::new_in(FixedAlloc::new(metadata)))
    }

    pub fn with_capacity(metadata: <T as Pointee>::Metadata, capacity: usize) -> Self {
        let alloc = FixedAlloc::new(metadata);
        let layout = unsafe { alloc.layout() };
        Self(Vec::with_capacity_in(capacity * layout.size(), alloc))
    }

    fn metadata(&self) -> <T as Pointee>::Metadata {
        self.0.allocator().metadata()
    }

    unsafe fn layout(&self) -> Layout {
        self.0.allocator().layout()
    }

    fn item_size(&self) -> usize {
        unsafe { self.layout() }.size()
    }

    fn start_end_index(&self, index: usize) -> (usize, usize) {
        let start = index * self.item_size();
        let end = start + self.item_size();
        (start, end)
    }

    unsafe fn raw(&self, index: usize) -> &T {
        let (start, end) = self.start_end_index(index);
        let slice = self.0.get_unchecked(start..end);
        &*std::ptr::from_raw_parts(slice.as_ptr() as *mut (), self.metadata())
    }

    unsafe fn raw_mut(&mut self, index: usize) -> &mut T {
        let (start, end) = self.start_end_index(index);
        let slice = self.0.get_unchecked_mut(start..end);
        &mut *std::ptr::from_raw_parts_mut(slice.as_mut_ptr() as *mut (), self.metadata())
    }

    pub fn capacity(&self) -> usize {
        self.0.capacity() / self.item_size()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional * self.item_size())
    }

    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }

    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity * self.item_size())
    }

    pub fn truncate(&mut self, len: usize) {
        if len < self.len() {
            for i in len..self.len() {
                unsafe {
                    let raw = self.raw_mut(i);
                    drop_in_place(raw)
                }
            }
            self.0.truncate(len * self.item_size())
        }
    }

    pub fn as_ptr(&self) -> *const T {
        unsafe { self.raw(0) }
    }

    pub fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { self.raw_mut(0) }
    }

    pub unsafe fn set_len(&mut self, new_len: usize) {
        self.0.set_len(new_len * self.item_size())
    }

    unsafe fn copy_to_box(&self, index: usize) -> Box<T> {
        let layout = self.layout();
        if let Ok(ptr) = Global.allocate(layout) {
            let ptr = ptr.as_mut_ptr();
            ptr.copy_from_nonoverlapping(
                self.0.as_ptr().add(index * self.item_size()),
                self.item_size(),
            );
            Box::from_raw(std::ptr::from_raw_parts_mut(
                ptr as *mut (),
                self.metadata(),
            ))
        } else {
            handle_alloc_error(layout)
        }
    }

    pub fn swap_remove(&mut self, index: usize) -> Box<T> {
        let index = index * self.item_size();
        let last_index = (self.len() - 1) * self.item_size();
        unsafe {
            std::ptr::swap_nonoverlapping(
                self.0.as_mut_ptr().add(index),
                self.0.as_mut_ptr().add(last_index),
                self.item_size(),
            );
            self.set_len(self.len() - 1);
            self.copy_to_box(self.len())
        }
    }

    pub fn insert(&mut self, index: usize, element: Box<T>) {
        let (ptr, metadata) = (element.as_ref() as *const T).to_raw_parts();
        if metadata != self.metadata() {
            panic!("Different metadata.");
        }
        self.reserve(1);
        let (start, end) = self.start_end_index(index);
        unsafe {
            std::ptr::copy(
                self.0.as_ptr().add(start),
                self.0.as_mut_ptr().add(end),
                self.len() - index,
            );
            std::ptr::copy_nonoverlapping(
                ptr as *const u8,
                self.0.as_mut_ptr().add(start),
                self.item_size(),
            );
            forget(element);
            self.set_len(self.len() + 1);
        }
    }

    pub unsafe fn insert_with(&mut self, index: usize, f: impl FnOnce(&mut T::Target))
    where
        T: MaybeUninitProject,
    {
        self.reserve(1);
        let (start, end) = self.start_end_index(index);
        unsafe {
            std::ptr::copy(
                self.0.as_ptr().add(start),
                self.0.as_mut_ptr().add(end),
                self.len() - index,
            );
            let ptr = std::ptr::from_raw_parts_mut::<T::Target>(
                self.0.as_mut_ptr().add(start) as *mut (),
                self.metadata(),
            );
            f(&mut *ptr);
            self.set_len(self.len() + 1);
        }
    }

    pub fn remove(&mut self, index: usize) -> Box<T> {
        unsafe {
            let b = self.copy_to_box(index);

            let (start, end) = self.start_end_index(index);
            std::ptr::copy(
                self.0.as_ptr().add(end),
                self.0.as_mut_ptr().add(start),
                self.len() - index - 1,
            );
            self.set_len(self.len() - 1);

            b
        }
    }

    pub fn push(&mut self, value: Box<T>) {
        self.insert(self.len(), value);
    }

    pub unsafe fn push_with(&mut self, f: impl FnOnce(&mut T::Target))
    where
        T: MaybeUninitProject,
    {
        self.insert_with(self.len(), f);
    }

    pub fn pop(&mut self) -> Option<Box<T>> {
        if self.is_empty() {
            None
        } else {
            Some(self.remove(self.len() - 1))
        }
    }

    pub fn clear(&mut self) {
        for i in 0..self.len() {
            unsafe {
                let raw = self.raw_mut(i);
                drop_in_place(raw)
            }
        }
        self.0.clear()
    }

    pub fn len(&self) -> usize {
        self.0.len() / self.item_size()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<T: ?Sized> Drop for FixedVec<T> {
    fn drop(&mut self) {
        self.clear()
    }
}

impl<T: ?Sized, I: SliceIndex<FixedVec<T>>> Index<I> for FixedVec<T> {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        index.index(self)
    }
}

impl<T: ?Sized, I: SliceIndex<FixedVec<T>>> IndexMut<I> for FixedVec<T> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        index.index_mut(self)
    }
}

unsafe impl<T: ?Sized> SliceIndex<FixedVec<T>> for usize {
    type Output = T;

    fn get(self, slice: &FixedVec<T>) -> Option<&Self::Output> {
        if self < slice.len() {
            Some(unsafe { slice.raw(self) })
        } else {
            None
        }
    }

    fn get_mut(self, slice: &mut FixedVec<T>) -> Option<&mut Self::Output> {
        if self < slice.len() {
            Some(unsafe { slice.raw_mut(self) })
        } else {
            None
        }
    }

    unsafe fn get_unchecked(self, slice: *const FixedVec<T>) -> *const Self::Output {
        (*slice).raw(self)
    }

    unsafe fn get_unchecked_mut(self, slice: *mut FixedVec<T>) -> *mut Self::Output {
        (*slice).raw_mut(self)
    }

    fn index(self, slice: &FixedVec<T>) -> &Self::Output {
        self.get(slice).expect("Index out of bound.")
    }

    fn index_mut(self, slice: &mut FixedVec<T>) -> &mut Self::Output {
        self.get_mut(slice).expect("Index out of bound.")
    }
}

unsafe impl<T: ?Sized> SliceIndex<FixedVec<T>> for RangeFull {
    type Output = FixedVec<T>;

    fn get(self, slice: &FixedVec<T>) -> Option<&Self::Output> {
        Some(slice)
    }

    fn get_mut(self, slice: &mut FixedVec<T>) -> Option<&mut Self::Output> {
        Some(slice)
    }

    unsafe fn get_unchecked(self, slice: *const FixedVec<T>) -> *const Self::Output {
        slice
    }

    unsafe fn get_unchecked_mut(self, slice: *mut FixedVec<T>) -> *mut Self::Output {
        slice
    }

    fn index(self, slice: &FixedVec<T>) -> &Self::Output {
        slice
    }

    fn index_mut(self, slice: &mut FixedVec<T>) -> &mut Self::Output {
        slice
    }
}

#[cfg(test)]
mod test {
    use crate::*;
    use std::sync::Arc;

    #[test]
    fn basic() {
        let mut vec: FixedVec<UnsizedSlice<u32, u64>> = FixedVec::new(6);
        assert_eq!(vec.len(), 0);
        vec.push(unsafe {
            Box::<UnsizedSlice<u32, u64>>::new_unsized_with(6, |slice| {
                slice.header.write(114514);
                MaybeUninit::write_slice(&mut slice.slice, &[1, 1, 4, 5, 1, 4]);
            })
        });
        assert_eq!(vec.len(), 1);
        assert_eq!(&vec[0].header, &114514);
        assert_eq!(&vec[0].slice, &[1, 1, 4, 5, 1, 4]);
    }

    #[test]
    fn in_place() {
        let mut vec: FixedVec<UnsizedSlice<u32, u64>> = FixedVec::new(6);
        assert_eq!(vec.len(), 0);
        unsafe {
            vec.push_with(|slice| {
                slice.header.write(114514);
                MaybeUninit::write_slice(&mut slice.slice, &[1, 1, 4, 5, 1, 4]);
            })
        };
        assert_eq!(vec.len(), 1);
        assert_eq!(&vec[0].header, &114514);
        assert_eq!(&vec[0].slice, &[1, 1, 4, 5, 1, 4]);
    }

    #[test]
    fn untrivial_drop() {
        let data = Arc::new(());

        let mut vec: FixedVec<UnsizedSlice<Arc<()>, Arc<()>>> = FixedVec::new(2);
        unsafe {
            vec.push_with(|slice| {
                slice.header.write(data.clone());
                MaybeUninit::write_slice_cloned(&mut slice.slice, &[data.clone(), data.clone()]);
            });
        }
        assert_eq!(Arc::strong_count(&data), 4);

        drop(vec);
        assert_eq!(Arc::strong_count(&data), 1);
    }

    #[test]
    #[should_panic(expected = "Different metadata.")]
    fn different_meta() {
        let mut vec: FixedVec<UnsizedSlice<u32, u64>> = FixedVec::new(6);
        vec.push(unsafe {
            Box::<UnsizedSlice<u32, u64>>::new_unsized_with(3, |slice| {
                slice.header.write(114514);
                MaybeUninit::write_slice(&mut slice.slice, &[1, 1, 4]);
            })
        });
    }
}
