const WORD_LEN: usize = std::mem::size_of::<usize>() * 8;

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
            words: vec![Self::words_for(len)],
            len: len,
        }
    }

    pub fn from_bits<'a, I>(bits: I) -> Self
    where
        I: Iterator<Item = &'a bool>,
    {
        let mut this = Self::new();
        for &b in bits {
            this.push(b);
        }
        this
    }

    #[inline(always)]
    pub fn get_bit(&self, pos: usize) -> bool {
        debug_assert!(pos < self.len);
        let block = pos / WORD_LEN;
        let shift = pos % WORD_LEN;
        (self.words[block] >> shift) & 1 == 1
    }

    #[inline(always)]
    pub fn set_bit(&mut self, pos: usize, b: bool) {
        debug_assert!(pos < self.len);
        let wpos = pos / WORD_LEN;
        let pos_in_word = pos % WORD_LEN;
        self.words[wpos] &= !(1 << pos_in_word);
        self.words[wpos] |= (b as usize) << pos_in_word;
    }

    #[inline(always)]
    pub fn push(&mut self, b: bool) {
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
    pub fn get_word(&self, wpos: usize) -> usize {
        self.words[wpos]
    }

    #[inline(always)]
    pub fn num_words(&self) -> usize {
        self.words.len()
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    fn words_for(n: usize) -> usize {
        (n + WORD_LEN - 1) / WORD_LEN
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tiny_bit_vector() {
        let bits = vec![
            true, false, false, true, false, true, false, false, false, true, true, false, false,
            false, true, true, true, false, true, false, true, false, false, false, true,
        ];
        let mut bv = BitVector::new();
        bits.iter().for_each(|&b| bv.push(b));

        assert_eq!(bits.len(), bv.len());
        for i in 0..bits.len() {
            assert_eq!(bits[i], bv.get_bit(i));
        }
    }
}
