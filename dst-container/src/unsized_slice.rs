use crate::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, MaybeUninitProject, UnsizedClone)]
#[repr(C)]
/// Represents a [`Sized`] header and an unsized slice.
pub struct UnsizedSlice<H, T> {
    /// The header.
    pub header: H,
    /// The unsized slice.
    pub slice: [T],
}

#[cfg(test)]
mod test {
    use crate::*;
    use std::sync::Arc;

    #[test]
    fn new_box() {
        let b = unsafe {
            Box::<UnsizedSlice<u32, u64>>::new_unsized_with(6, |slice| {
                slice.header.write(114514u32);
                MaybeUninit::copy_from_slice(&mut slice.slice, &[1u64, 1, 4, 5, 1, 4]);
            })
        };
        assert_eq!(b.header, 114514);
        assert_eq!(b.slice, [1, 1, 4, 5, 1, 4]);
    }

    #[test]
    fn zeroed() {
        let b: Box<UnsizedSlice<_, _>> =
            unsafe { Box::<UnsizedSlice<u64, u128>>::new_zeroed_unsized(6).assume_init() };
        assert_eq!(b.header, 0);
        assert_eq!(b.slice, [0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn untrivial_drop() {
        let data = Arc::new(());

        let b = unsafe {
            Box::<UnsizedSlice<Arc<()>, Arc<()>>>::new_unsized_with(2, |slice| {
                slice.header.write(data.clone());
                MaybeUninit::clone_from_slice(&mut slice.slice, &[data.clone(), data.clone()]);
            })
        };
        assert_eq!(Arc::strong_count(&data), 4);

        let b_clone = b.clone();
        assert_eq!(Arc::strong_count(&data), 7);

        drop(b_clone);
        drop(b);
        assert_eq!(Arc::strong_count(&data), 1);
    }
}
