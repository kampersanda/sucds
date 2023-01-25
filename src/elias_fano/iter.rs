//! Iterator on EliasFano.
#![cfg(target_pointer_width = "64")]

use crate::bit_vector::unary::UnaryIter;
use crate::EliasFano;

/// Iterator for enumerating integers stored in [`EliasFano`], created by [`EliasFano::iter`].
pub struct Iter<'a> {
    ef: &'a EliasFano,
    k: usize,
    high_iter: Option<UnaryIter<'a>>,
    low_buf: usize,
    low_mask: usize,
    chunks_in_word: usize,
    chunks_avail: usize,
}

impl<'a> Iter<'a> {
    /// Creates an iterator for enumerating integers from position `k`.
    pub fn new(ef: &'a EliasFano, k: usize) -> Self {
        debug_assert!(ef.low_len < 64);
        debug_assert!(!ef.high_bits_d1.is_empty());

        let low_buf = 0;
        let low_mask = (1 << ef.low_len) - 1;

        let (chunks_in_word, chunks_avail) = if ef.low_len != 0 {
            (64 / ef.low_len, 0)
        } else {
            (0, ef.len())
        };

        let high_iter = if k < ef.len() {
            let pos = ef.high_bits_d1.select(&ef.high_bits, k).unwrap();
            Some(ef.high_bits.unary_iter(pos))
        } else {
            None
        };

        Self {
            ef,
            k,
            high_iter,
            low_buf,
            low_mask,
            chunks_in_word,
            chunks_avail,
        }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.k == self.ef.high_bits_d1.len() {
            self.high_iter = None;
        }
        if let Some(high_iter) = &mut self.high_iter {
            if self.chunks_avail == 0 {
                self.low_buf = self
                    .ef
                    .low_bits
                    .get_word64(self.k * self.ef.low_len)
                    .unwrap();
                self.chunks_avail = self.chunks_in_word - 1;
            } else {
                self.chunks_avail -= 1;
            }
            let high = high_iter.next().unwrap();
            let low = self.low_buf & self.low_mask;
            let ret = ((high - self.k) << self.ef.low_len) | low;
            self.k += 1;
            self.low_buf >>= self.ef.low_len;
            Some(ret)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn gen_random_bits(len: usize, seed: u64) -> Vec<bool> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen::<bool>()).collect()
    }

    fn test_iter(bits: &[bool], ef: &EliasFano) {
        let expected: Vec<usize> = bits
            .iter()
            .enumerate()
            .filter(|(_, &b)| b)
            .map(|(i, _)| i)
            .collect();
        for k in (0..expected.len()).step_by(100) {
            let mut it = ef.iter(k);
            for &exp in &expected[k..] {
                assert_eq!(it.next(), Some(exp));
            }
            assert_eq!(it.next(), None);
        }
    }

    #[test]
    fn test_tiny_bits() {
        let ef = EliasFano::from_bits([true, false, true, true, false, true, true]).unwrap();
        let mut it = ef.iter(0);
        assert_eq!(it.next(), Some(0));
        assert_eq!(it.next(), Some(2));
        assert_eq!(it.next(), Some(3));
        assert_eq!(it.next(), Some(5));
        assert_eq!(it.next(), Some(6));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_random_bits() {
        for seed in 0..100 {
            let bits = gen_random_bits(10000, seed);
            let ef = EliasFano::from_bits(bits.iter().cloned()).unwrap();
            test_iter(&bits, &ef);
        }
    }
}
