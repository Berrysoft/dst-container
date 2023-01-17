use crate::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, MaybeUninitProject)]
#[repr(C)]
/// Represents a [`Sized`] header and an unsized [`str`].
pub struct UnsizedStr<H> {
    /// The header.
    pub header: H,
    /// The unsized [`str`].
    pub str: str,
}

impl<H: UnsizedClone> UnsizedClone for UnsizedStr<H> {
    fn clone_to(&self, dest: &mut Self::Target) {
        self.header.clone_to(&mut dest.header);
        self.str.clone_to(&mut dest.str);
    }
}

#[cfg(test)]
mod test {
    use crate::*;

    #[test]
    fn new_box() {
        let b = unsafe {
            Box::<UnsizedStr<u32>>::new_unsized_with(5, |slice| {
                slice.header.write(114514);
                MaybeUninit::write_slice(&mut slice.str, "Hello".as_bytes());
            })
        };

        assert_eq!(b.header, 114514);
        assert_eq!(&b.str, "Hello");
    }
}
