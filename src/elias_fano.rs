#![cfg(target_pointer_width = "64")]

use crate::{broadword, BitVector, DArray};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct EliasFano {
    high_bits: BitVector,
    high_bits_d1: DArray,
    high_bits_d0: Option<DArray>,
    low_bits: BitVector,
    low_len: usize,
    universe: usize,
}

impl EliasFano {
    pub fn new(b: EliasFanoBuilder, with_rank_index: bool) -> Self {
        let high_bits_d1 = DArray::new(&b.high_bits, true);
        let high_bits_d0 = if with_rank_index {
            Some(DArray::new(&b.high_bits, false))
        } else {
            None
        };
        Self {
            high_bits: b.high_bits,
            high_bits_d1,
            high_bits_d0,
            low_bits: b.low_bits,
            low_len: b.low_len,
            universe: b.universe,
        }
    }

    pub fn from_bitvec(bv: &BitVector, with_rank_index: bool) -> Self {
        let n = bv.len();
        let m = (0..bv.num_words())
            .into_iter()
            .fold(0, |acc, i| acc + broadword::popcount(bv.get_word(i)));
        let mut b = EliasFanoBuilder::new(n, m);
        for i in 0..n {
            if bv.get_bit(i) {
                b.push(i);
            }
        }
        Self::new(b, with_rank_index)
    }

    pub fn select(&self, n: usize) -> usize {
        ((self.high_bits_d1.select(&self.high_bits, n) - n) << self.low_len)
            | self.low_bits.get_bits(n * self.low_len, self.low_len)
    }

    pub fn rank(&self, pos: usize) -> usize {
        debug_assert!(pos <= self.universe());
        debug_assert!(self.high_bits_d0.is_some());

        if pos == self.universe() {
            return self.len();
        }

        let high_bits_d0 = self.high_bits_d0.as_ref().unwrap();

        let h_rank = pos >> self.low_len;
        let mut h_pos = high_bits_d0.select(&self.high_bits, h_rank);
        let mut rank = h_pos - h_rank;
        let l_pos = pos & ((1 << self.low_len) - 1);

        while h_pos > 0
            && self.high_bits.get_bit(h_pos - 1)
            && self
                .low_bits
                .get_bits((rank - 1) * self.low_len, self.low_len)
                >= l_pos
        {
            rank -= 1;
            h_pos -= 1;
        }

        rank
    }

    pub fn predecessor(&self, pos: usize) -> Option<usize> {
        Some(self.rank(pos + 1))
            .filter(|&i| i > 0)
            .map(|i| self.select(i - 1))
    }

    pub fn successor(&self, pos: usize) -> Option<usize> {
        Some(self.rank(pos))
            .filter(|&i| i < self.len())
            .map(|i| self.select(i))
    }

    pub fn len(&self) -> usize {
        self.high_bits_d1.len()
    }

    pub fn universe(&self) -> usize {
        self.universe
    }
}

pub struct EliasFanoBuilder {
    high_bits: BitVector,
    low_bits: BitVector,
    universe: usize,
    num_ints: usize,
    pos: usize,
    last: usize,
    low_len: usize,
}

impl EliasFanoBuilder {
    pub fn new(universe: usize, num_ints: usize) -> Self {
        assert_ne!(universe, 0);
        assert_ne!(num_ints, 0);
        let low_len = broadword::msb(universe / num_ints).unwrap_or(0);
        Self {
            high_bits: BitVector::with_len((num_ints + 1) + (universe >> low_len) + 1),
            low_bits: BitVector::new(),
            universe,
            num_ints,
            pos: 0,
            last: 0,
            low_len,
        }
    }

    pub fn push(&mut self, i: usize) {
        assert!(i >= self.last && i <= self.universe);
        assert!(self.pos < self.num_ints);
        self.last = i;
        let low_mask = (1 << self.low_len) - 1;
        if self.low_len != 0 {
            self.low_bits.push_bits(i & low_mask, self.low_len);
        }
        self.high_bits.set_bit((i >> self.low_len) + self.pos, true);
        self.pos += 1;
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

    fn test_rank_select(bits: &[bool], ef: &EliasFano) {
        let mut cur_rank = 0;
        for i in 0..bits.len() {
            assert_eq!(cur_rank, ef.rank(i));
            if bits[i] {
                assert_eq!(i, ef.select(cur_rank));
                cur_rank += 1;
            }
        }
        assert_eq!(cur_rank, ef.len());
        assert_eq!(bits.len(), ef.universe());
    }

    fn test_successor_predecessor(bits: &[bool], ef: &EliasFano) {
        let one_positions: Vec<usize> = (0..bits.len()).filter(|&i| bits[i]).collect();

        let mut pos = 0;
        for &i in &one_positions {
            let next = ef.successor(pos).unwrap();
            debug_assert_eq!(i, next);
            pos = next + 1;
        }
        debug_assert!(pos == ef.universe() || ef.successor(pos).is_none());

        let mut pos = bits.len() - 1;
        for &i in one_positions.iter().rev() {
            let pred = ef.predecessor(pos).unwrap();
            debug_assert_eq!(i, pred);
            if pred == 0 {
                pos = ef.universe();
                break;
            }
            pos = pred - 1;
        }
        debug_assert!(pos == ef.universe() || ef.predecessor(pos).is_none());
    }

    #[test]
    fn test_tiny_bits() {
        let bv = BitVector::from_bits(&[true, false, false, true, false, true, true]);
        let ef = EliasFano::from_bitvec(&bv, false);
        assert_eq!(ef.select(0), 0);
        assert_eq!(ef.select(1), 3);
        assert_eq!(ef.select(2), 5);
        assert_eq!(ef.select(3), 6);
    }

    #[test]
    fn test_random_bits() {
        for seed in 0..100 {
            let bits = gen_random_bits(10000, seed);
            let bv = BitVector::from_bits(&bits);
            let ef = EliasFano::from_bitvec(&bv, true);
            test_rank_select(&bits, &ef);
            test_successor_predecessor(&bits, &ef);
        }
    }

    #[test]
    fn test_serialize() {
        let bits = gen_random_bits(10000, 42);
        let bv = BitVector::from_bits(&bits);
        let ef = EliasFano::from_bitvec(&bv, true);
        let bytes = bincode::serialize(&ef).unwrap();
        let other: EliasFano = bincode::deserialize(&bytes).unwrap();
        assert_eq!(ef.len(), other.len());
        assert_eq!(ef.universe(), other.universe());
        test_rank_select(&bits, &other);
        test_successor_predecessor(&bits, &other);
    }
}
