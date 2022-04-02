use crate::BitVector;

/// Iterator for enumerating bits, created by [`BitVector::iter`].
pub struct Iter<'a> {
    bv: &'a BitVector,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub fn new(bv: &'a BitVector) -> Self {
        Self { bv, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = bool;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.bv.len() {
            let x = self.bv.get_bit(self.pos);
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.bv.len(), Some(self.bv.len()))
    }
}
