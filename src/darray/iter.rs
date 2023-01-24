//! Iterator on DArray.
use crate::{DArray, Selector};

/// Iterator for enumerating integers, created by [`DArray::iter`].
pub struct Iter<'a> {
    da: &'a DArray,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(da: &'a DArray) -> Self {
        Self { da, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.da.len() {
            let x = self.da.select1(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.da.len(), Some(self.da.len()))
    }
}
