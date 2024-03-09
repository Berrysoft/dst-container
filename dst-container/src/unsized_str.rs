use crate::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, MaybeUninitProject, UnsizedClone)]
#[repr(C)]
/// Represents a [`Sized`] header and an unsized [`str`].
pub struct UnsizedStr<H> {
    /// The header.
    pub header: H,
    /// The unsized [`str`].
    pub str: str,
}

#[cfg(test)]
mod test {
    use crate::*;

    #[test]
    fn new_box() {
        let b = unsafe {
            Box::<UnsizedStr<u32>>::new_unsized_with(5, |slice| {
                slice.header.write(114514);
                MaybeUninit::copy_from_slice(&mut slice.str, "Hello".as_bytes());
            })
        };

        assert_eq!(b.header, 114514);
        assert_eq!(&b.str, "Hello");
    }
}
