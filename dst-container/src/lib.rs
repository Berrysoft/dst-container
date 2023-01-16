//! This is a crate providing functionalities creating DST instances.

#![feature(allocator_api)]
#![feature(layout_for_ptr)]
#![feature(maybe_uninit_write_slice)]
#![feature(ptr_metadata)]
#![warn(missing_docs)]

use std::{
    alloc::{handle_alloc_error, AllocError, Allocator, Global, Layout},
    mem::MaybeUninit,
    ptr::{NonNull, Pointee},
    rc::Rc,
    sync::Arc,
};

pub use dst_container_derive::MaybeUninitProject;

mod unsized_slice;
pub use unsized_slice::UnsizedSlice;

/// A DST with maybe-uninit project defined.
pub trait MaybeUninitProject {
    /// The maybe-uninit project type.
    /// [`MaybeUninit`] can only deal with [`Sized`] types.
    type Target: ?Sized + Pointee<Metadata = <Self as Pointee>::Metadata>;
}

impl<T> MaybeUninitProject for [T] {
    type Target = [MaybeUninit<T>];
}

/// An abstract of smart pointers.
pub trait SmartPtr: Sized {
    /// The inner type of the pointer.
    type Content: ?Sized;

    /// Rebind the smart pointer to another content type.
    type Rebind<U: ?Sized>: SmartPtr<Content = U>;

    /// Create the smart pointer from pointer allocated from [`Global`].
    /// # Safety
    /// See `Box::from_raw`.
    unsafe fn from_alloc(p: *mut Self::Content) -> Self;

    /// Convert the smart pointer to another content type one.
    /// # Safety
    /// See [`std::mem::transmute`].
    unsafe fn rebind<U: ?Sized>(self) -> Self::Rebind<U>
    where
        U: Pointee<Metadata = <Self::Content as Pointee>::Metadata>;
}

impl<T: ?Sized> SmartPtr for Box<T> {
    type Content = T;

    type Rebind<U: ?Sized> = Box<U>;

    unsafe fn from_alloc(p: *mut Self::Content) -> Self {
        Self::from_raw(p)
    }

    unsafe fn rebind<U: ?Sized>(self) -> Self::Rebind<U>
    where
        U: Pointee<Metadata = <Self::Content as Pointee>::Metadata>,
    {
        let (ptr, metadata) = Box::into_raw(self).to_raw_parts();
        Box::from_raw(std::ptr::from_raw_parts_mut(ptr, metadata))
    }
}

impl<T: ?Sized> SmartPtr for Rc<T> {
    type Content = T;

    type Rebind<U: ?Sized> = Rc<U>;

    unsafe fn from_alloc(p: *mut Self::Content) -> Self {
        Box::from_alloc(p).into()
    }

    unsafe fn rebind<U: ?Sized>(self) -> Self::Rebind<U>
    where
        U: Pointee<Metadata = <Self::Content as Pointee>::Metadata>,
    {
        let (ptr, metadata) = Rc::into_raw(self).to_raw_parts();
        Rc::from_raw(std::ptr::from_raw_parts(ptr, metadata))
    }
}

impl<T: ?Sized> SmartPtr for Arc<T> {
    type Content = T;

    type Rebind<U: ?Sized> = Arc<U>;

    unsafe fn from_alloc(p: *mut Self::Content) -> Self {
        Box::from_alloc(p).into()
    }

    unsafe fn rebind<U: ?Sized>(self) -> Self::Rebind<U>
    where
        U: Pointee<Metadata = <Self::Content as Pointee>::Metadata>,
    {
        let (ptr, metadata) = Arc::into_raw(self).to_raw_parts();
        Arc::from_raw(std::ptr::from_raw_parts(ptr, metadata))
    }
}

type RebindPtr<P, U> = <P as SmartPtr>::Rebind<U>;

mod sealed {
    pub trait Sealed {}
}

use sealed::Sealed;
impl<P: SmartPtr> Sealed for P {}

/// Provide functions for smart pointers to create DST instances on heap.
pub trait NewUninit: Sealed + SmartPtr
where
    Self::Content: MaybeUninitProject,
{
    /// Create maybe-uninit DST.
    fn new_uninit_unsized(
        metadata: <Self::Content as Pointee>::Metadata,
    ) -> RebindPtr<Self, <Self::Content as MaybeUninitProject>::Target> {
        unsafe {
            RebindPtr::<Self, <Self::Content as MaybeUninitProject>::Target>::from_alloc(
                alloc_with_metadata::<Self::Content>(metadata),
            )
        }
    }

    /// Create maybe-uninit zero-initialized DST.
    fn new_zeroed_unsized(
        metadata: <Self::Content as Pointee>::Metadata,
    ) -> RebindPtr<Self, <Self::Content as MaybeUninitProject>::Target> {
        unsafe {
            RebindPtr::<Self, <Self::Content as MaybeUninitProject>::Target>::from_alloc(
                zeroed_with_metadata::<Self::Content>(metadata),
            )
        }
    }

    /// Create DST and initialize the instance with user-provided function.
    /// # Safety
    /// The caller should ensure all fields are properly initialized.
    unsafe fn new_unsized_with(
        metadata: <Self::Content as Pointee>::Metadata,
        f: impl FnOnce(&mut <Self::Content as MaybeUninitProject>::Target),
    ) -> Self
    // To make compiler happy.
    where
        Self::Rebind<<Self::Content as MaybeUninitProject>::Target>:
            SmartPtr<Rebind<Self::Content> = Self>,
    {
        let ptr = alloc_with_metadata::<Self::Content>(metadata);
        f(&mut *ptr);
        RebindPtr::<Self, <Self::Content as MaybeUninitProject>::Target>::from_alloc(ptr)
            .rebind::<Self::Content>()
    }
}

impl<P: SmartPtr> NewUninit for P where P::Content: MaybeUninitProject {}

/// Provide `assume_init` for smart pointers of maybe-uninit project types.
pub trait AssumeInit<T: ?Sized + MaybeUninitProject>:
    Sealed + SmartPtr<Content = T::Target>
{
    /// Converts to initialized smart pointer.
    /// # Safety
    /// See `MaybeUninit::assume_init`.
    unsafe fn assume_init_unsized(self) -> RebindPtr<Self, T> {
        self.rebind()
    }
}

impl<T: ?Sized + MaybeUninitProject, P: SmartPtr<Content = T::Target>> AssumeInit<T> for P {}

unsafe fn alloc_with_metadata_impl<T: ?Sized + MaybeUninitProject>(
    metadata: <T as Pointee>::Metadata,
    alloc: impl FnOnce(Layout) -> Result<NonNull<[u8]>, AllocError>,
) -> *mut T::Target {
    let null_ptr: *mut T = std::ptr::from_raw_parts_mut(std::ptr::null_mut(), metadata);
    let layout = Layout::for_value_raw(null_ptr);
    if let Ok(ptr) = alloc(layout) {
        std::ptr::from_raw_parts_mut(ptr.as_ptr() as *mut (), metadata)
    } else {
        handle_alloc_error(layout)
    }
}

unsafe fn alloc_with_metadata<T: ?Sized + MaybeUninitProject>(
    metadata: <T as Pointee>::Metadata,
) -> *mut T::Target {
    alloc_with_metadata_impl::<T>(metadata, |layout| Global.allocate(layout))
}

unsafe fn zeroed_with_metadata<T: ?Sized + MaybeUninitProject>(
    metadata: <T as Pointee>::Metadata,
) -> *mut T::Target {
    alloc_with_metadata_impl::<T>(metadata, |layout| Global.allocate_zeroed(layout))
}

#[cfg(test)]
mod test {
    use crate::*;

    #[derive(MaybeUninitProject)]
    #[repr(transparent)]
    struct SliceWrapper([u8]);

    #[test]
    fn slice_wrapper() {
        let s: Box<SliceWrapper> =
            unsafe { Box::<SliceWrapper>::new_zeroed_unsized(64).assume_init_unsized() };
        assert_eq!(&s.0, &[0u8; 64]);

        let s: Rc<SliceWrapper> =
            unsafe { Rc::<SliceWrapper>::new_zeroed_unsized(64).assume_init_unsized() };
        assert_eq!(&s.0, &[0u8; 64]);

        let s: Arc<SliceWrapper> =
            unsafe { Arc::<SliceWrapper>::new_zeroed_unsized(64).assume_init_unsized() };
        assert_eq!(&s.0, &[0u8; 64]);
    }
}