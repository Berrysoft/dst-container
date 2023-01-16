//! This is a crate providing functionalities creating DST instances.

#![feature(allocator_api)]
#![feature(layout_for_ptr)]
#![feature(maybe_uninit_write_slice)]
#![feature(ptr_metadata)]
#![warn(missing_docs)]

use std::{mem::MaybeUninit, ptr::Pointee};

pub use dst_container_derive::MaybeUninitProject;

mod smart_ptr;
pub use smart_ptr::{AssumeInit, NewUninit, SmartPtr};

mod unsized_slice;
pub use unsized_slice::UnsizedSlice;

mod unsized_str;
pub use unsized_str::UnsizedStr;

mod fixed_vec;
pub use fixed_vec::FixedVec;

/// A DST with maybe-uninit project defined.
pub trait MaybeUninitProject {
    /// The maybe-uninit project type.
    /// [`MaybeUninit`] can only deal with [`Sized`] types.
    type Target: ?Sized + Pointee<Metadata = <Self as Pointee>::Metadata>;
}

impl<T: Sized> MaybeUninitProject for T {
    type Target = MaybeUninit<T>;
}

impl<T> MaybeUninitProject for [T] {
    type Target = [MaybeUninit<T>];
}

impl MaybeUninitProject for str {
    type Target = [MaybeUninit<u8>];
}
