//! Iterator on [`DacsList`].

use crate::DacsList;

/// Iterator for enumerating integers, created by [`DacsList::iter()`].
pub struct Iter<'a> {
    list: &'a DacsList,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(list: &'a DacsList) -> Self {
        Self { list, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.list.len() {
            let x = self.list.get(self.pos);
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len(), Some(self.list.len()))
    }
}
