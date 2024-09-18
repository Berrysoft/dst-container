//! This is a crate providing functionalities creating DST instances.

#![feature(allocator_api)]
#![feature(layout_for_ptr)]
#![feature(maybe_uninit_write_slice)]
#![feature(ptr_metadata)]
#![feature(slice_index_methods)]
#![feature(slice_ptr_get)]
#![feature(specialization)]
#![cfg_attr(test, feature(new_zeroed_alloc, test))]
#![allow(incomplete_features)]
#![warn(missing_docs)]

#[cfg(test)]
extern crate test;

use std::{mem::MaybeUninit, ptr::Pointee};

#[doc(no_inline)]
pub use dst_container_derive::{MaybeUninitProject, UnsizedClone};

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

/// Provide the ability to duplicate a DST object.
pub trait UnsizedClone: MaybeUninitProject {
    /// Clone the current type to maybe-uninit target.
    fn clone_to(&self, dest: &mut Self::Target);

    /// Returns a boxed copy of the boxed value.
    ///
    /// Only apply to [`Box`] because [`Rc`] and [`Arc`] have own clone impl.
    ///
    /// [`Rc`]: std::rc::Rc
    /// [`Arc`]: std::sync::Arc
    #[allow(clippy::borrowed_box)]
    fn clone(self: &Box<Self>) -> Box<Self> {
        let (_, metadata) = (self.as_ref() as *const Self).to_raw_parts();
        unsafe { Box::<Self>::new_unsized_with(metadata, |dest| self.as_ref().clone_to(dest)) }
    }
}

impl<T: Clone> UnsizedClone for T {
    fn clone_to(&self, dest: &mut Self::Target) {
        dest.write(self.clone());
    }
}

impl<T: UnsizedClone> UnsizedClone for [T] {
    default fn clone_to(&self, _dest: &mut Self::Target) {
        // All Sized Clone implements UnsizedClone.
        unreachable!()
    }
}

impl<T: Clone> UnsizedClone for [T] {
    default fn clone_to(&self, dest: &mut Self::Target) {
        MaybeUninit::clone_from_slice(dest, self);
    }
}

impl<T: Copy> UnsizedClone for [T] {
    fn clone_to(&self, dest: &mut Self::Target) {
        MaybeUninit::copy_from_slice(dest, self);
    }
}

impl UnsizedClone for str {
    fn clone_to(&self, dest: &mut Self::Target) {
        MaybeUninit::copy_from_slice(dest, self.as_bytes());
    }
}
