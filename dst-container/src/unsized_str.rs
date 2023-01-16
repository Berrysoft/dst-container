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

impl<H: Clone> Clone for Box<UnsizedStr<H>> {
    fn clone(&self) -> Self {
        unsafe {
            Self::new_unsized_with(self.str.len(), |slice| {
                slice.header.write(self.header.clone());
                MaybeUninit::write_slice(&mut slice.str, self.str.as_bytes());
            })
        }
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
