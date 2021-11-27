#![cfg(target_pointer_width = "64")]

use crate::{broadword, BitVector, DArray};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct EliasFano {
    high_bits: BitVector,
    high_bits_d1: DArray,
    low_bits: BitVector,
    l: usize,
    universe: usize,
}

impl EliasFano {
    pub fn new(b: EliasFanoBuilder) -> Self {
        Self {
            high_bits_d1: DArray::new(&b.high_bits),
            high_bits: b.high_bits,
            low_bits: b.low_bits,
            l: b.l,
            universe: b.n,
        }
    }

    pub fn from_bitvec(bv: &BitVector) -> Self {
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
        Self::new(b)
    }

    pub fn select(&self, n: usize) -> usize {
        ((self.high_bits_d1.select(&self.high_bits, n) - n) << self.l)
            | self.low_bits.get_bits(n * self.l, self.l)
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
    n: usize, // universe
    m: usize, // num integers
    pos: usize,
    last: usize,
    l: usize,
}

impl EliasFanoBuilder {
    pub fn new(n: usize, m: usize) -> Self {
        assert_ne!(n, 0);
        assert_ne!(m, 0);
        let l = broadword::msb(n / m).unwrap_or(0);
        Self {
            high_bits: BitVector::with_len((m + 1) + (n >> l) + 1),
            low_bits: BitVector::new(),
            n,
            m,
            pos: 0,
            last: 0,
            l,
        }
    }

    pub fn push(&mut self, i: usize) {
        assert!(i >= self.last && i <= self.n);
        assert!(self.pos < self.m);
        self.last = i;
        let low_mask = (1 << self.l) - 1;
        if self.l != 0 {
            self.low_bits.push_bits(i & low_mask, self.l);
        }
        self.high_bits.set_bit((i >> self.l) + self.pos, true);
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

    fn test_select(bits: &[bool], ef: &EliasFano) {
        let mut cur_rank = 0;
        for i in 0..bits.len() {
            if bits[i] {
                assert_eq!(i, ef.select(cur_rank));
                cur_rank += 1;
            }
        }
        assert_eq!(cur_rank, ef.len());
    }

    #[test]
    fn test_tiny_bits() {
        let bv = BitVector::from_bits(&[true, false, false, true, false, true, true]);
        let ef = EliasFano::from_bitvec(&bv);
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
            let ef = EliasFano::from_bitvec(&bv);
            test_select(&bits, &ef);
        }
    }

    #[test]
    fn test_serialize() {
        let bits = gen_random_bits(10000, 42);
        let bv = BitVector::from_bits(&bits);
        let ef = EliasFano::from_bitvec(&bv);
        let bytes = bincode::serialize(&ef).unwrap();
        let other: EliasFano = bincode::deserialize(&bytes).unwrap();
        assert_eq!(ef.len(), other.len());
        assert_eq!(ef.universe(), other.universe());
        test_select(&bits, &other);
    }
}
