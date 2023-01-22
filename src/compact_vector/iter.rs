//! Iterator on compact vectors.
use crate::{CompactVector, IntArray};

/// Iterator for enumerating integers, created by [`CompactVector::iter`].
pub struct Iter<'a> {
    cv: &'a CompactVector,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(cv: &'a CompactVector) -> Self {
        Self { cv, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.cv.len() {
            let x = self.cv.get(self.pos);
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.cv.len(), Some(self.cv.len()))
    }
}
