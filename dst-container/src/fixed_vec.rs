use crate::*;
use std::{
    alloc::{handle_alloc_error, AllocError, Allocator, Global, Layout},
    iter::FusedIterator,
    mem::forget,
    ops::{Index, IndexMut, RangeFull},
    ptr::{drop_in_place, NonNull, Pointee},
    slice::SliceIndex,
};

#[derive(Clone, Copy)]
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

    #[inline]
    pub const fn metadata(&self) -> <T as Pointee>::Metadata {
        self.metadata
    }

    #[inline]
    pub unsafe fn layout(&self) -> Layout {
        Layout::for_value_raw(std::ptr::from_raw_parts::<T>(
            std::ptr::null(),
            self.metadata,
        ))
    }

    #[inline]
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

/// A vector designed for DST.
pub struct FixedVec<T: ?Sized>(Vec<u8, FixedAlloc<T>>);

impl<T: ?Sized> FixedVec<T> {
    /// Constructs a new, empty `FixedVec<T>`, with provided metadata.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// # use dst_container::*;
    /// let mut vec: FixedVec<UnsizedSlice<u32, u64>> = FixedVec::new(6);
    /// ```
    pub const fn new(metadata: <T as Pointee>::Metadata) -> Self {
        Self(Vec::new_in(FixedAlloc::new(metadata)))
    }

    /// Constructs a new, empty `FixedVec<T>`.
    /// The metadata is obtained from the provided pointer.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// # use dst_container::*;
    /// let array = [0u32, 1, 2];
    /// let mut vec: FixedVec<[u32]> = FixedVec::new_like(array.as_slice());
    /// ```
    pub const fn new_like(ptr: *const T) -> Self {
        let (_, metadata) = ptr.to_raw_parts();
        Self::new(metadata)
    }

    /// Constructs a new, empty `FixedVec<T>` with at least the specified capacity.
    pub fn with_capacity(metadata: <T as Pointee>::Metadata, capacity: usize) -> Self {
        let alloc = FixedAlloc::new(metadata);
        let layout = unsafe { alloc.layout() };
        Self(Vec::with_capacity_in(capacity * layout.size(), alloc))
    }

    /// Constructs a new, empty `FixedVec<T>` with at least the specified capacity.
    /// The metadata is obtained from the provided pointer.
    pub fn with_capacity_like(ptr: *const T, capacity: usize) -> Self {
        let (_, metadata) = ptr.to_raw_parts();
        Self::with_capacity(metadata, capacity)
    }

    #[inline]
    fn metadata(&self) -> <T as Pointee>::Metadata {
        self.0.allocator().metadata()
    }

    #[inline]
    unsafe fn layout(&self) -> Layout {
        self.0.allocator().layout()
    }

    #[inline]
    fn item_size(&self) -> usize {
        unsafe { self.layout() }.size()
    }

    #[inline]
    fn start_end_index(&self, index: usize) -> (usize, usize) {
        let start = index * self.item_size();
        let end = start + self.item_size();
        (start, end)
    }

    #[inline]
    unsafe fn raw(&self, index: usize) -> &T {
        let (start, end) = self.start_end_index(index);
        let slice = self.0.get_unchecked(start..end);
        &*std::ptr::from_raw_parts(slice.as_ptr() as *mut (), self.metadata())
    }

    #[inline]
    unsafe fn raw_mut(&mut self, index: usize) -> &mut T {
        let (start, end) = self.start_end_index(index);
        let slice = self.0.get_unchecked_mut(start..end);
        &mut *std::ptr::from_raw_parts_mut(slice.as_mut_ptr() as *mut (), self.metadata())
    }

    /// Returns the total number of elements the vector can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut vec: FixedVec<UnsizedSlice<u32, u32>> = FixedVec::with_capacity(3, 10);
    /// // SAFETY: u32 is trivial.
    /// unsafe{ vec.push_with(|_| {}) };
    /// assert_eq!(vec.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.0.capacity() / self.item_size()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `FixedVec<T>`. The collection may reserve more space to
    /// speculatively avoid frequent reallocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional * self.item_size())
    }

    /// Shrinks the capacity of the vector as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator
    /// may still inform the vector that there is space for a few more elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut vec: FixedVec<UnsizedSlice<u32, u32>> = FixedVec::with_capacity(3, 10);
    /// // SAFETY: u32 is trivial.
    /// unsafe{ vec.push_with(|_| {}) };
    /// assert_eq!(vec.capacity(), 10);
    /// vec.shrink_to_fit();
    /// assert!(vec.capacity() >= 1);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }

    /// Shrinks the capacity of the vector with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut vec: FixedVec<UnsizedSlice<u32, u32>> = FixedVec::with_capacity(3, 10);
    /// // SAFETY: u32 is trivial.
    /// unsafe{ vec.push_with(|_| {}) };
    /// assert_eq!(vec.capacity(), 10);
    /// vec.shrink_to(2);
    /// assert!(vec.capacity() >= 2);
    /// vec.shrink_to(0);
    /// assert!(vec.capacity() >= 1);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity * self.item_size())
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater than the vector's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// Truncating a five element vector to two elements:
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut vec: FixedVec<UnsizedSlice<u32, u32>> = FixedVec::with_capacity(3, 10);
    /// // SAFETY: u32 is trivial.
    /// unsafe{ vec.push_with(|slice| { slice.header.write(1); }) };
    /// unsafe{ vec.push_with(|slice| { slice.header.write(2); }) };
    /// unsafe{ vec.push_with(|slice| { slice.header.write(3); }) };
    /// vec.truncate(2);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(vec[0].header, 1);
    /// assert_eq!(vec[1].header, 2);
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the vector's current
    /// length:
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut vec: FixedVec<UnsizedSlice<u32, u32>> = FixedVec::with_capacity(3, 10);
    /// // SAFETY: u32 is trivial.
    /// unsafe{ vec.push_with(|slice| { slice.header.write(1); }) };
    /// unsafe{ vec.push_with(|slice| { slice.header.write(2); }) };
    /// unsafe{ vec.push_with(|slice| { slice.header.write(3); }) };
    /// vec.truncate(8);
    /// assert_eq!(vec.len(), 3);
    /// assert_eq!(vec[0].header, 1);
    /// assert_eq!(vec[1].header, 2);
    /// assert_eq!(vec[2].header, 3);
    /// ```
    ///
    /// Truncating when `len == 0` is equivalent to calling the [`clear`]
    /// method.
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut vec: FixedVec<UnsizedSlice<u32, u32>> = FixedVec::with_capacity(3, 10);
    /// // SAFETY: u32 is trivial.
    /// unsafe{ vec.push_with(|slice| { slice.header.write(1); }) };
    /// unsafe{ vec.push_with(|slice| { slice.header.write(2); }) };
    /// unsafe{ vec.push_with(|slice| { slice.header.write(3); }) };
    /// vec.truncate(0);
    /// assert_eq!(vec.len(), 0);
    /// ```
    ///
    /// [`clear`]: FixedVec::clear
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

    /// Returns a raw pointer to the vector's buffer, or a dangling raw pointer
    /// valid for zero sized reads if the vector didn't allocate.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up pointing to garbage.
    /// Modifying the vector may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// The caller must also ensure that the memory the pointer (non-transitively) points to
    /// is never written to (except inside an `UnsafeCell`) using this pointer or any pointer
    /// derived from it. If you need to mutate the contents of the slice, use [`as_mut_ptr`].
    ///
    /// [`as_mut_ptr`]: FixedVec::as_mut_ptr
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        unsafe { self.raw(0) }
    }

    /// Returns an unsafe mutable pointer to the vector's buffer, or a dangling
    /// raw pointer valid for zero sized reads if the vector didn't allocate.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up pointing to garbage.
    /// Modifying the vector may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(ptr_metadata)]
    /// # use dst_container::*;
    ///
    /// // Allocate vector big enough for 1 elements.
    /// let size = 1;
    /// let mut x: FixedVec<UnsizedSlice<u32, u32>> = FixedVec::with_capacity(2, size);
    /// let x_ptr = x.as_mut_ptr();
    ///
    /// // Initialize elements via raw pointer writes, then set length.
    /// unsafe {
    ///     let u32_ptr = x_ptr.to_raw_parts().0 as *mut u32;
    ///     for i in 0..3 {
    ///         *u32_ptr.add(i) = i as u32;
    ///     }
    ///     x.set_len(size);
    /// }
    /// assert_eq!(x[0].header, 0);
    /// assert_eq!(&x[0].slice, &[1, 2]);
    /// ```
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { self.raw_mut(0) }
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// This is a low-level operation that maintains none of the normal
    /// invariants of the type. Normally changing the length of a vector
    /// is done using one of the safe operations instead, such as
    /// [`truncate`], [`extend`], or [`clear`].
    ///
    /// [`truncate`]: FixedVec::truncate
    /// [`extend`]: Extend::extend
    /// [`clear`]: FixedVec::clear
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`capacity()`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`capacity()`]: FixedVec::capacity
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

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is *O*(1).
    /// If you need to preserve the element order, use [`remove`] instead.
    ///
    /// [`remove`]: FixedVec::remove
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut v = FixedVec::<str>::new(3);
    /// v.push(Box::from("foo"));
    /// v.push(Box::from("bar"));
    /// v.push(Box::from("baz"));
    /// v.push(Box::from("qux"));
    ///
    /// assert_eq!(v.swap_remove(1).as_ref(), "bar");
    /// assert_eq!(&v[1], "qux");
    ///
    /// assert_eq!(v.swap_remove(0).as_ref(), "foo");
    /// assert_eq!(&v[0], "baz");
    /// ```
    pub fn swap_remove(&mut self, index: usize) -> Box<T> {
        let len = self.len();
        if index >= len {
            panic!("swap_remove index (is {index}) should be < len (is {len})");
        }
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

    #[allow(clippy::comparison_chain)]
    unsafe fn insert_raw(&mut self, index: usize, f: impl FnOnce(*mut u8)) {
        self.reserve(1);
        let (start, end) = self.start_end_index(index);
        let len = self.len();
        unsafe {
            if index < len {
                std::ptr::copy(
                    self.0.as_ptr().add(start),
                    self.0.as_mut_ptr().add(end),
                    (len - index) * self.item_size(),
                );
            } else if index == len {
                // Nop.
            } else {
                panic!("insertion index (is {index}) should be <= len (is {len})");
            }
            f(self.0.as_mut_ptr().add(start));
            self.set_len(len + 1);
        }
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(maybe_uninit_write_slice)]
    /// # use dst_container::*;
    /// # use std::mem::MaybeUninit;
    ///
    /// let mut vec = FixedVec::<[i32]>::new(2);
    /// unsafe {
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[1, 1]); });
    ///     vec.insert(0, Box::<[i32]>::new_zeroed_unsized(2).assume_init_unsized());
    /// }
    /// assert_eq!(&vec[0], [0, 0]);
    /// assert_eq!(&vec[1], [1, 1]);
    /// ```
    pub fn insert(&mut self, index: usize, element: Box<T>) {
        let (ptr, metadata) = (element.as_ref() as *const T).to_raw_parts();
        if metadata != self.metadata() {
            panic!("Different metadata.");
        }
        let item_size = self.item_size();
        unsafe {
            self.insert_raw(index, |dest| {
                std::ptr::copy_nonoverlapping(ptr as *const u8, dest as *mut u8, item_size);
            });
        }
        forget(element);
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Safety
    /// The caller should ensure the new element being initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(maybe_uninit_write_slice)]
    /// # use dst_container::*;
    /// # use std::mem::MaybeUninit;
    ///
    /// let mut vec = FixedVec::<[i32]>::new(2);
    /// unsafe {
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[1, 1]); });
    ///     vec.insert_with(0, |slice| { MaybeUninit::write_slice(slice, &[0, 0]); });
    /// }
    /// assert_eq!(&vec[0], [0, 0]);
    /// assert_eq!(&vec[1], [1, 1]);
    /// ```
    pub unsafe fn insert_with(&mut self, index: usize, f: impl FnOnce(&mut T::Target))
    where
        T: MaybeUninitProject,
    {
        let metadata = self.metadata();
        self.insert_raw(index, |dest| {
            let ptr = std::ptr::from_raw_parts_mut::<T::Target>(dest as *mut (), metadata);
            f(&mut *ptr);
        });
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(maybe_uninit_write_slice)]
    /// # use dst_container::*;
    /// # use std::mem::MaybeUninit;
    ///
    /// let mut vec = FixedVec::<[i32]>::new(2);
    /// unsafe {
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[0, 0]); });
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[1, 1]); });
    /// }
    /// assert_eq!(vec.remove(0).as_ref(), &[0, 0]);
    /// assert_eq!(&vec[0], &[1, 1]);
    /// ```
    pub fn remove(&mut self, index: usize) -> Box<T> {
        let len = self.len();
        if index >= len {
            panic!("removal index (is {index}) should be < len (is {len})");
        }
        let (start, end) = self.start_end_index(index);
        unsafe {
            let b;
            {
                b = self.copy_to_box(index);

                std::ptr::copy(
                    self.0.as_ptr().add(end),
                    self.0.as_mut_ptr().add(start),
                    (len - index - 1) * self.item_size(),
                );
            }
            self.set_len(len - 1);
            b
        }
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    #[inline]
    pub fn push(&mut self, value: Box<T>) {
        self.insert(self.len(), value);
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Safety
    ///
    /// The same as [`insert_with`].
    ///
    /// [`insert_with`]: FixedVec::insert_with
    #[inline]
    pub unsafe fn push_with(&mut self, f: impl FnOnce(&mut T::Target))
    where
        T: MaybeUninitProject,
    {
        self.insert_with(self.len(), f);
    }

    /// Removes the last element from a vector and returns it, or [`None`] if it
    /// is empty.
    pub fn pop(&mut self) -> Option<Box<T>> {
        if self.is_empty() {
            None
        } else {
            Some(self.remove(self.len() - 1))
        }
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut vec = FixedVec::<[i32]>::new(2);
    /// unsafe {
    ///     vec.push_with(|slice| {});
    ///     vec.push_with(|slice| {});
    /// }
    /// vec.clear();
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.truncate(0)
    }

    /// Returns the number of elements in the vector, also referred to
    /// as its 'length'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut vec = FixedVec::<[i32]>::new(2);
    /// unsafe {
    ///     vec.push_with(|slice| {});
    ///     vec.push_with(|slice| {});
    /// }
    /// assert_eq!(vec.len(), 2);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len() / self.item_size()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use dst_container::*;
    /// let mut vec = FixedVec::<[i32]>::new(2);
    /// assert!(vec.is_empty());
    /// unsafe {
    ///     vec.push_with(|slice| {});
    ///     vec.push_with(|slice| {});
    /// }
    /// assert!(!vec.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    /// Returns an iterator over the vector.
    ///
    /// The iterator yields all items from start to end.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(maybe_uninit_write_slice)]
    /// # use dst_container::*;
    /// # use std::mem::MaybeUninit;
    ///
    /// let mut vec = FixedVec::<[i32]>::new(2);
    /// unsafe {
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[0, 0]); });
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[1, 1]); });
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[2, 2]); });
    /// }
    ///
    /// let mut iterator = vec.iter();
    ///
    /// assert_eq!(iterator.next(), Some(&[0, 0][..]));
    /// assert_eq!(iterator.next(), Some(&[1, 1][..]));
    /// assert_eq!(iterator.next(), Some(&[2, 2][..]));
    /// assert_eq!(iterator.next(), None);
    /// ```
    #[inline]
    pub fn iter(&self) -> FixedVecIter<T> {
        FixedVecIter::new(self)
    }

    /// Returns an iterator that allows modifying each value.
    ///
    /// The iterator yields all items from start to end.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(maybe_uninit_write_slice)]
    /// # use dst_container::*;
    /// # use std::mem::MaybeUninit;
    ///
    /// let mut vec = FixedVec::<[i32]>::new(2);
    /// unsafe {
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[0, 0]); });
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[1, 1]); });
    ///     vec.push_with(|slice| { MaybeUninit::write_slice(slice, &[2, 2]); });
    /// }
    ///
    /// for elem in vec.iter_mut() {
    ///     elem[0] += 2;
    ///     elem[1] *= 2;
    /// }
    ///
    /// let mut iterator = vec.iter();
    ///
    /// assert_eq!(iterator.next(), Some(&[2, 0][..]));
    /// assert_eq!(iterator.next(), Some(&[3, 2][..]));
    /// assert_eq!(iterator.next(), Some(&[4, 4][..]));
    /// assert_eq!(iterator.next(), None);
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> FixedVecIterMut<T> {
        FixedVecIterMut::new(self)
    }

    /// Returns a reference to an element or subslice depending on the type of
    /// index.
    ///
    /// - If given a position, returns a reference to the element at that
    ///   position or `None` if out of bounds.
    /// - If given a range, returns the subslice corresponding to that range,
    ///   or `None` if out of bounds.
    #[inline]
    pub fn get<I: SliceIndex<Self>>(&self, index: I) -> Option<&I::Output> {
        index.get(self)
    }

    /// Returns a mutable reference to an element or subslice depending on the
    /// type of index (see [`get`]) or `None` if the index is out of bounds.
    ///
    /// [`get`]: FixedVec::get
    #[inline]
    pub fn get_mut<I: SliceIndex<Self>>(&mut self, index: I) -> Option<&mut I::Output> {
        index.get_mut(self)
    }

    /// Returns a reference to an element or subslice, without doing bounds
    /// checking.
    ///
    /// For a safe alternative see [`get`].
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used.
    ///
    /// [`get`]: FixedVec::get
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_unchecked<I: SliceIndex<Self>>(&self, index: I) -> &I::Output {
        &*index.get_unchecked(self)
    }

    /// Returns a mutable reference to an element or subslice, without doing
    /// bounds checking.
    ///
    /// For a safe alternative see [`get_mut`].
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is *[undefined behavior]*
    /// even if the resulting reference is not used.
    ///
    /// [`get_mut`]: FixedVec::get_mut
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_unchecked_mut<I: SliceIndex<Self>>(&mut self, index: I) -> &mut I::Output {
        &mut *index.get_unchecked_mut(self)
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

pub struct FixedVecIter<'a, T: ?Sized> {
    vec: &'a FixedVec<T>,
    index: usize,
}

impl<'a, T: ?Sized> FixedVecIter<'a, T> {
    pub(crate) fn new(vec: &'a FixedVec<T>) -> Self {
        Self { vec, index: 0 }
    }
}

impl<'a, T: ?Sized> Iterator for FixedVecIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.vec.len() {
            let res = Some(unsafe { self.vec.get_unchecked(self.index) });
            self.index += 1;
            res
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.vec.len();
        (len, Some(len))
    }

    fn count(self) -> usize {
        self.vec.len()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.vec.get(n)
    }
}

impl<T: ?Sized> ExactSizeIterator for FixedVecIter<'_, T> {}

impl<'a, T: ?Sized> DoubleEndedIterator for FixedVecIter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index > 0 {
            self.index -= 1;
            Some(unsafe { self.vec.get_unchecked(self.index) })
        } else {
            None
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if n >= self.vec.len() {
            None
        } else {
            Some(unsafe { self.vec.get_unchecked(self.vec.len() - n - 1) })
        }
    }
}

impl<T: ?Sized> FusedIterator for FixedVecIter<'_, T> {}

impl<'a, T: ?Sized> IntoIterator for &'a FixedVec<T> {
    type Item = &'a T;

    type IntoIter = FixedVecIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct FixedVecIterMut<'a, T: ?Sized> {
    vec: &'a mut FixedVec<T>,
    index: usize,
}

impl<'a, T: ?Sized> FixedVecIterMut<'a, T> {
    pub(crate) fn new(vec: &'a mut FixedVec<T>) -> Self {
        Self { vec, index: 0 }
    }
}

impl<'a, T: ?Sized> Iterator for FixedVecIterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.vec.len() {
            let res = Some(unsafe { self.vec.get_unchecked_mut(self.index) });
            self.index += 1;
            res.map(|p| unsafe { &mut *(p as *mut T) })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.vec.len();
        (len, Some(len))
    }

    fn count(self) -> usize {
        self.vec.len()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.vec.get_mut(n).map(|p| unsafe { &mut *(p as *mut T) })
    }
}

impl<T: ?Sized> ExactSizeIterator for FixedVecIterMut<'_, T> {}

impl<'a, T: ?Sized> DoubleEndedIterator for FixedVecIterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index > 0 {
            self.index -= 1;
            Some(unsafe { &mut *(self.vec.get_unchecked_mut(self.index) as *mut T) })
        } else {
            None
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if n >= self.vec.len() {
            None
        } else {
            Some(unsafe { &mut *(self.vec.get_unchecked_mut(self.vec.len() - n - 1) as *mut T) })
        }
    }
}

impl<T: ?Sized> FusedIterator for FixedVecIterMut<'_, T> {}

impl<'a, T: ?Sized> IntoIterator for &'a mut FixedVec<T> {
    type Item = &'a mut T;

    type IntoIter = FixedVecIterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: ?Sized> Extend<Box<T>> for FixedVec<T> {
    fn extend<I: IntoIterator<Item = Box<T>>>(&mut self, iter: I) {
        for item in iter {
            self.push(item);
        }
    }
}

impl<T: ?Sized + UnsizedClone> Clone for FixedVec<T> {
    fn clone(&self) -> Self {
        let mut vec = FixedVec::<T>::with_capacity(self.metadata(), self.len());
        for item in self {
            unsafe {
                vec.push_with(|dest| item.clone_to(dest));
            }
        }
        vec
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
    fn clone() {
        let mut vec = FixedVec::<[i32]>::new(2);
        vec.push(Box::from([1, 1]));
        vec.push(Box::from([2, 2]));
        vec.push(Box::from([3, 3]));
        assert_eq!(&vec[0], &[1, 1]);
        assert_eq!(&vec[1], &[2, 2]);
        assert_eq!(&vec[2], &[3, 3]);

        let vec2 = vec.clone();
        assert_eq!(&vec2[0], &[1, 1]);
        assert_eq!(&vec2[1], &[2, 2]);
        assert_eq!(&vec2[2], &[3, 3]);
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
