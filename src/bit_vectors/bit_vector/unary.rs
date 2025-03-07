//! Unary iterator on bit vectors.
use super::WORD_LEN;
use crate::bit_vectors::BitVector;
use crate::bit_vectors::NumBits;
use crate::broadword;

/// Iterator for enumerating positions of set bits, created by [`BitVector::unary_iter`].
pub struct UnaryIter<'a> {
    bv: &'a BitVector,
    pos: usize,
    buf: usize,
}

impl<'a> UnaryIter<'a> {
    /// Creates the iterator from the given bit position.
    pub fn new(bv: &'a BitVector, pos: usize) -> Self {
        let buf = bv.words()[pos / WORD_LEN] & (usize::MAX.wrapping_shl((pos % WORD_LEN) as u32));
        Self { bv, pos, buf }
    }

    /// Gets the current bit position.
    #[inline(always)]
    pub const fn position(&self) -> usize {
        self.pos
    }

    /// Skips to the `k`-th one after the current position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([false, true, false, false, true, true]);
    /// let mut it = bv.unary_iter(0);
    ///
    /// assert_eq!(it.skip1(0), Some(1));
    /// assert_eq!(it.skip1(1), Some(4));
    /// assert_eq!(it.skip1(2), None);
    /// ```
    #[inline(always)]
    pub fn skip1(&mut self, k: usize) -> Option<usize> {
        let mut skipped = 0;
        let mut buf = self.buf;
        loop {
            let w = broadword::popcount(buf);
            if skipped + w > k {
                break;
            }
            skipped += w;
            self.pos += WORD_LEN;
            let word_pos = self.pos / WORD_LEN;
            if self.bv.num_words() <= word_pos {
                return None;
            }
            buf = self.bv.words()[word_pos];
        }
        debug_assert!(buf != 0);
        let pos_in_word = broadword::select_in_word(buf, k - skipped).unwrap();
        self.buf = buf & usize::MAX.wrapping_shl(pos_in_word as u32);
        self.pos = (self.pos & !(WORD_LEN - 1)) + pos_in_word;
        Some(self.pos)
    }

    /// Skips to the `k`-th zero after the current position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([false, true, false, false, true, true]);
    /// let mut it = bv.unary_iter(0);
    ///
    /// assert_eq!(it.skip0(0), Some(0));
    /// assert_eq!(it.skip0(1), Some(2));
    /// assert_eq!(it.skip0(2), None);
    /// ```
    #[inline(always)]
    pub fn skip0(&mut self, k: usize) -> Option<usize> {
        let mut skipped = 0;
        let pos_in_word = self.pos % WORD_LEN;
        let mut buf = !self.buf & usize::MAX.wrapping_shl(pos_in_word as u32);
        loop {
            let w = broadword::popcount(buf);
            if skipped + w > k {
                break;
            }
            skipped += w;
            self.pos += WORD_LEN;
            let word_pos = self.pos / WORD_LEN;
            if self.bv.num_words() <= word_pos {
                return None;
            }
            buf = !self.bv.words()[word_pos];
        }
        debug_assert!(buf != 0);
        let pos_in_word = broadword::select_in_word(buf, k - skipped).unwrap();
        self.buf = !buf & usize::MAX.wrapping_shl(pos_in_word as u32);
        self.pos = (self.pos & !(WORD_LEN - 1)) + pos_in_word;
        Some(self.pos).filter(|&x| x < self.bv.num_bits())
    }
}

impl Iterator for UnaryIter<'_> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut buf = self.buf;
        while buf == 0 {
            self.pos += WORD_LEN;
            let word_pos = self.pos / WORD_LEN;
            if self.bv.num_words() <= word_pos {
                return None;
            }
            buf = self.bv.words()[word_pos];
        }
        let pos_in_word = broadword::lsb(buf).unwrap();
        self.buf = buf & (buf - 1); // clear LSB
        self.pos = (self.pos & !(WORD_LEN - 1)) + pos_in_word;
        Some(self.pos)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_next_all_zeros() {
        let bv = BitVector::from_bit(false, 100);
        let mut it = bv.unary_iter(0);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_skip1_all_zeros() {
        let bv = BitVector::from_bit(false, 100);
        let mut it = bv.unary_iter(0);
        assert_eq!(it.skip1(0), None);
    }

    #[test]
    fn test_skip0_all_ones() {
        let bv = BitVector::from_bit(true, 100);
        let mut it = bv.unary_iter(0);
        assert_eq!(it.skip0(0), None);
    }
}
