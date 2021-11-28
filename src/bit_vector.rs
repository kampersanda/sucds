use crate::broadword;
use serde::{Deserialize, Serialize};

const WORD_LEN: usize = std::mem::size_of::<usize>() * 8;

#[derive(Serialize, Deserialize)]
pub struct BitVector {
    words: Vec<usize>,
    len: usize,
}

impl BitVector {
    pub fn new() -> Self {
        Self {
            words: vec![],
            len: 0,
        }
    }

    pub fn with_len(len: usize) -> Self {
        Self {
            words: vec![0; Self::words_for(len)],
            len: len,
        }
    }

    pub fn from_bits<'a, I>(bits: I) -> Self
    where
        I: IntoIterator<Item = &'a bool>,
    {
        let mut this = Self::new();
        bits.into_iter().for_each(|&b| this.push_bit(b));
        this
    }

    #[inline(always)]
    pub fn get_bit(&self, pos: usize) -> bool {
        debug_assert!(pos < self.len);
        let (block, shift) = (pos / WORD_LEN, pos % WORD_LEN);
        (self.words[block] >> shift) & 1 == 1
    }

    #[inline(always)]
    pub fn get_bits(&self, pos: usize, len: usize) -> usize {
        debug_assert!(len <= WORD_LEN);
        debug_assert!(pos + len <= self.len());
        if len == 0 {
            return 0;
        }
        let (block, shift) = (pos / WORD_LEN, pos % WORD_LEN);
        let mask = {
            if len < WORD_LEN {
                (1 << len) - 1
            } else {
                std::usize::MAX
            }
        };
        if shift + len <= WORD_LEN {
            self.words[block] >> shift & mask
        } else {
            (self.words[block] >> shift) | (self.words[block + 1] << (WORD_LEN - shift) & mask)
        }
    }

    #[inline(always)]
    pub fn set_bit(&mut self, pos: usize, bit: bool) {
        debug_assert!(pos < self.len);
        let word = pos / WORD_LEN;
        let pos_in_word = pos % WORD_LEN;
        self.words[word] &= !(1 << pos_in_word);
        self.words[word] |= (bit as usize) << pos_in_word;
    }

    #[inline(always)]
    pub fn set_bits(&mut self, pos: usize, bits: usize, len: usize) {
        debug_assert!(len <= WORD_LEN);
        debug_assert!(pos + len <= self.len());
        debug_assert!(len == WORD_LEN || (bits >> len) == 0);
        if len == 0 {
            return;
        }
        let mask = {
            if len < WORD_LEN {
                (1 << len) - 1
            } else {
                std::usize::MAX
            }
        };
        let word = pos / WORD_LEN;
        let pos_in_word = pos % WORD_LEN;

        self.words[word] &= !(mask << pos_in_word);
        self.words[word] |= bits << pos_in_word;

        let stored = WORD_LEN - pos_in_word;
        if stored < len {
            self.words[word + 1] &= !(mask >> stored);
            self.words[word + 1] |= bits >> stored;
        }
    }

    #[inline(always)]
    pub fn push_bit(&mut self, b: bool) {
        let pos_in_word = self.len % WORD_LEN;
        if pos_in_word == 0 {
            self.words.push(b as usize);
        } else {
            let cur_word = self.words.last_mut().unwrap();
            *cur_word |= (b as usize) << pos_in_word;
        }
        self.len += 1;
    }

    #[inline(always)]
    pub fn push_bits(&mut self, bits: usize, len: usize) {
        debug_assert!(len <= WORD_LEN);
        debug_assert!(len == WORD_LEN || (bits >> len) == 0);
        if len == 0 {
            return;
        }
        let pos_in_word = self.len % WORD_LEN;
        if pos_in_word == 0 {
            self.words.push(bits);
        } else {
            let cur_word = self.words.last_mut().unwrap();
            *cur_word |= bits << pos_in_word;
            if len > 64 - pos_in_word {
                self.words.push(bits >> (64 - pos_in_word));
            }
        }
        self.len += len;
    }

    pub fn predecessor1(&self, pos: usize) -> Option<usize> {
        debug_assert!(pos < self.len());
        let mut block = pos / WORD_LEN;
        let shift = WORD_LEN - pos % WORD_LEN - 1;
        let mut word = (self.words[block] << shift) >> shift;
        loop {
            if let Some(ret) = broadword::msb(word) {
                return Some(block * 64 + ret);
            } else if block == 0 {
                return None;
            }
            block -= 1;
            word = self.words[block];
        }
    }

    pub fn successor1(&self, pos: usize) -> Option<usize> {
        debug_assert!(pos < self.len());
        let mut block = pos / WORD_LEN;
        let shift = pos % WORD_LEN;
        let mut word = (self.words[block] >> shift) << shift;
        loop {
            if let Some(ret) = broadword::lsb(word) {
                return Some(block * 64 + ret).filter(|&i| i < self.len());
            }
            block += 1;
            if block == self.words.len() {
                return None;
            }
            word = self.words[block];
        }
    }

    pub fn predecessor0(&self, pos: usize) -> Option<usize> {
        debug_assert!(pos < self.len());
        let mut block = pos / WORD_LEN;
        let shift = WORD_LEN - pos % WORD_LEN - 1;
        let mut word = (!self.words[block] << shift) >> shift;
        loop {
            if let Some(ret) = broadword::msb(word) {
                return Some(block * 64 + ret);
            } else if block == 0 {
                return None;
            }
            block -= 1;
            word = !self.words[block];
        }
    }

    pub fn successor0(&self, pos: usize) -> Option<usize> {
        debug_assert!(pos < self.len());
        let mut block = pos / WORD_LEN;
        let shift = pos % WORD_LEN;
        let mut word = (!self.words[block] >> shift) << shift;
        loop {
            if let Some(ret) = broadword::lsb(word) {
                return Some(block * 64 + ret).filter(|&i| i < self.len());
            }
            block += 1;
            if block == self.words.len() {
                return None;
            }
            word = !self.words[block];
        }
    }

    #[inline(always)]
    pub fn get_word(&self, word_pos: usize) -> usize {
        self.words[word_pos]
    }

    #[inline(always)]
    pub fn num_words(&self) -> usize {
        self.words.len()
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn shrink_to_fit(&mut self) {
        self.words.shrink_to_fit();
    }

    #[inline(always)]
    fn words_for(n: usize) -> usize {
        (n + WORD_LEN - 1) / WORD_LEN
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

    fn gen_random_ints(len: usize, width: usize, seed: u64) -> Vec<usize> {
        let mask = (1 << width) - 1;
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen::<usize>() & mask).collect()
    }

    fn test_bit_vector(bits: &[bool]) {
        let bv = BitVector::from_bits(bits);
        assert_eq!(bits.len(), bv.len());
        for i in 0..bits.len() {
            assert_eq!(bits[i], bv.get_bit(i));
        }

        let mut other = BitVector::with_len(bits.len());
        assert_eq!(bv.len(), other.len());
        bits.iter()
            .enumerate()
            .for_each(|(i, &b)| other.set_bit(i, b));
        for i in 0..bv.len() {
            assert_eq!(bv.get_bit(i), other.get_bit(i));
        }

        let one_positions: Vec<usize> = (0..bv.len()).filter(|&i| bv.get_bit(i)).collect();
        let zero_positions: Vec<usize> = (0..bv.len()).filter(|&i| !bv.get_bit(i)).collect();

        let mut pos = 0;
        for &i in &one_positions {
            let next = bv.successor1(pos).unwrap();
            debug_assert_eq!(i, next);
            pos = next + 1;
        }
        debug_assert!(pos == bv.len() || bv.successor1(pos).is_none());

        let mut pos = bv.len() - 1;
        for &i in one_positions.iter().rev() {
            let pred = bv.predecessor1(pos).unwrap();
            debug_assert_eq!(i, pred);
            if pred == 0 {
                pos = bv.len();
                break;
            }
            pos = pred - 1;
        }
        debug_assert!(pos == bv.len() || bv.predecessor1(pos).is_none());

        let mut pos = 0;
        for &i in &zero_positions {
            let next = bv.successor0(pos).unwrap();
            debug_assert_eq!(i, next);
            pos = next + 1;
        }
        debug_assert!(pos == bv.len() || bv.successor0(pos).is_none());

        let mut pos = bv.len() - 1;
        for &i in zero_positions.iter().rev() {
            let pred = bv.predecessor0(pos).unwrap();
            debug_assert_eq!(i, pred);
            if pred == 0 {
                pos = bv.len();
                break;
            }
            pos = pred - 1;
        }
        debug_assert!(pos == bv.len() || bv.predecessor0(pos).is_none());
    }

    fn test_int_vector(ints: &[usize], width: usize) {
        {
            let mut bv = BitVector::new();
            ints.iter().for_each(|&x| bv.push_bits(x, width));
            assert_eq!(ints.len() * width, bv.len());
            for i in 0..ints.len() {
                assert_eq!(ints[i], bv.get_bits(i * width, width));
            }
        }
        {
            let mut bv = BitVector::with_len(ints.len() * width);
            assert_eq!(ints.len() * width, bv.len());
            ints.iter()
                .enumerate()
                .for_each(|(i, &x)| bv.set_bits(i * width, x, width));
            for i in 0..ints.len() {
                assert_eq!(ints[i], bv.get_bits(i * width, width));
            }
        }
    }

    #[test]
    fn test_random_bits() {
        for seed in 0..100 {
            let bits = gen_random_bits(10000, seed);
            test_bit_vector(&bits);
        }
    }

    #[test]
    fn test_random_ints() {
        let mut rng = ChaChaRng::seed_from_u64(13);
        for seed in 0..100 {
            let width = rng.gen_range(1..16);
            let ints = gen_random_ints(10000, width, seed);
            test_int_vector(&ints, width);
        }
    }

    #[test]
    fn test_serialize() {
        let bv = BitVector::from_bits(&gen_random_bits(10000, 42));
        let bytes = bincode::serialize(&bv).unwrap();
        let other: BitVector = bincode::deserialize(&bytes).unwrap();
        assert_eq!(bv.len(), other.len());
        for i in 0..bv.len() {
            assert_eq!(bv.get_bit(i), other.get_bit(i));
        }
    }
}
