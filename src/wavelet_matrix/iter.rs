//! Iterator on WaveletMatrix.

use crate::WaveletMatrix;

/// Iterator for enumerating integers, created by [`WaveletMatrix::iter`].
pub struct Iter<'a> {
    wm: &'a WaveletMatrix,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(wm: &'a WaveletMatrix) -> Self {
        Self { wm, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // TODO: Optimization with caching.
        if self.pos < self.wm.len() {
            let x = self.wm.get(self.pos);
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.wm.len(), Some(self.wm.len()))
    }
}
