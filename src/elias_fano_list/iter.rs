//! Iterator on EliasFanoList.

use crate::{EliasFanoList, IntGetter};

/// Iterator for enumerating integers, created by [`EliasFanoList::iter`].
pub struct Iter<'a> {
    efl: &'a EliasFanoList,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(efl: &'a EliasFanoList) -> Self {
        Self { efl, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.efl.len() {
            let x = self.efl.get_int(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.efl.len(), Some(self.efl.len()))
    }
}
