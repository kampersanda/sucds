use crate::bit_vector::WORD_LEN;
use crate::broadword;
use crate::BitVector;

/// Iterator for enumerating positions of set bits.
///
/// # Examples
///
/// ```
/// use sucds::BitVector;
///
/// let bv = BitVector::from_bits([false, true, false, false, true]);
/// let mut it = bv.unary_iter(1);
///
/// assert_eq!(it.next(), Some(1));
/// assert_eq!(it.next(), Some(4));
/// assert_eq!(it.next(), None);
/// ```
pub struct UnaryIterator<'a> {
    bv: &'a BitVector,
    pos: usize,
    buf: usize,
}

impl<'a> UnaryIterator<'a> {
    /// Creates the iterator from the given bit position.
    pub fn new(bv: &'a BitVector, pos: usize) -> Self {
        let buf =
            bv.words()[pos / WORD_LEN] & (usize::max_value().wrapping_shl((pos % WORD_LEN) as u32));
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
    /// use sucds::BitVector;
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
        let pos_in_word = broadword::select_in_word(buf, k - skipped);
        self.buf = buf & usize::max_value().wrapping_shl(pos_in_word as u32);
        self.pos = (self.pos & !(WORD_LEN - 1)) + pos_in_word;
        Some(self.pos)
    }

    /// Skips to the `k`-th zero after the current position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
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
        let mut buf = !self.buf & usize::max_value().wrapping_shl(pos_in_word as u32);
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
        let pos_in_word = broadword::select_in_word(buf, k - skipped);
        self.buf = !buf & usize::max_value().wrapping_shl(pos_in_word as u32);
        self.pos = (self.pos & !(WORD_LEN - 1)) + pos_in_word;
        Some(self.pos).filter(|&x| x < self.bv.len())
    }
}

impl<'a> Iterator for UnaryIterator<'a> {
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

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn gen_random_bits(len: usize, p: f64, seed: u64) -> (Vec<bool>, usize) {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        let bits = (0..len).map(|_| rng.gen_bool(p)).collect();
        let pos = rng.gen_range(0..len);
        (bits, pos)
    }

    fn test_unary_iter(bits: &[bool], pos: usize) {
        let bv = BitVector::from_bits(bits.iter().cloned());

        let mut expected = vec![];
        for (i, &b) in bits[pos..].iter().enumerate() {
            if b {
                expected.push(pos + i);
            }
        }
        let mut it = bv.unary_iter(pos);
        for &ex in &expected {
            assert_eq!(it.next(), Some(ex));
        }
        assert_eq!(it.next(), None);
    }

    fn test_skip1(bits: &[bool], mut pos: usize) {
        let bv = BitVector::from_bits(bits.iter().cloned());
        pos = bv.successor1(pos).unwrap();

        let mut it = bv.unary_iter(pos);
        while let Some(i) = it.skip1(2) {
            pos = bv.successor1(pos + 1).unwrap();
            pos = bv.successor1(pos + 1).unwrap();
            assert_eq!(i, pos);
        }
    }

    fn test_skip0(bits: &[bool], mut pos: usize) {
        let bv = BitVector::from_bits(bits.iter().cloned());
        pos = bv.successor0(pos).unwrap();

        let mut it = bv.unary_iter(pos);
        while let Some(i) = it.skip0(2) {
            pos = bv.successor0(pos + 1).unwrap();
            pos = bv.successor0(pos + 1).unwrap();
            assert_eq!(i, pos);
        }
    }

    #[test]
    fn test_random_bits() {
        for seed in 0..100 {
            let (bits, pos) = gen_random_bits(10000, 0.5, seed);
            test_unary_iter(&bits, pos);
            test_skip1(&bits, pos);
            test_skip0(&bits, pos);
        }
    }

    #[test]
    fn test_sparse_random_bits() {
        for seed in 0..100 {
            let (bits, pos) = gen_random_bits(10000, 0.1, seed);
            test_unary_iter(&bits, pos);
            test_skip1(&bits, pos);
            test_skip0(&bits, pos);
        }
    }

    #[test]
    fn test_dense_random_bits() {
        for seed in 0..100 {
            let (bits, pos) = gen_random_bits(10000, 0.9, seed);
            test_unary_iter(&bits, pos);
            test_skip1(&bits, pos);
            test_skip0(&bits, pos);
        }
    }
}
