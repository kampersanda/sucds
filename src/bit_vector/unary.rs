use crate::bit_vector::WORD_LEN;
use crate::broadword;
use crate::BitVector;

pub struct UnaryIterator<'a> {
    bv: &'a BitVector,
    pos: usize,
    buf: usize,
}

impl<'a> UnaryIterator<'a> {
    pub fn new(bv: &'a BitVector, pos: usize) -> Self {
        let buf = bv.get_word(pos / WORD_LEN)
            & (usize::max_value().wrapping_shl((pos % WORD_LEN) as u32));
        Self { bv, pos, buf }
    }

    #[inline(always)]
    pub fn position(&self) -> usize {
        self.pos
    }

    // Skips to the k-th one after the current position
    #[inline(always)]
    pub fn skip(&mut self, k: usize) -> Option<usize> {
        let mut skipped = 0;
        let mut buf = self.buf;
        loop {
            let w = broadword::popcount(buf);
            if skipped + w > k {
                break;
            }
            skipped += w;
            self.pos += WORD_LEN;
            if self.bv.len() <= self.pos {
                return None;
            }
            buf = self.bv.get_word(self.pos / WORD_LEN);
        }
        debug_assert!(buf != 0);
        let pos_in_word = broadword::select_in_word(buf, k - skipped);
        self.buf = buf & usize::max_value().wrapping_shl(pos_in_word as u32);
        self.pos = (self.pos & !(WORD_LEN - 1)) + pos_in_word;
        Some(self.pos)
    }

    // skip to the k-th zero after the current position
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
            if self.bv.len() <= self.pos {
                return None;
            }
            buf = !self.bv.get_word(self.pos / WORD_LEN);
        }
        debug_assert!(buf != 0);
        let pos_in_word = broadword::select_in_word(buf, k - skipped);
        self.buf = !buf & usize::max_value().wrapping_shl(pos_in_word as u32);
        self.pos = (self.pos & !(WORD_LEN - 1)) + pos_in_word;
        Some(self.pos)
    }
}

impl<'a> Iterator for UnaryIterator<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let mut buf = self.buf;
        while buf == 0 {
            self.pos += WORD_LEN;
            if self.bv.len() <= self.pos {
                return None;
            }
            buf = self.bv.get_word(self.pos / WORD_LEN);
        }
        let pos_in_word = broadword::lsb(buf).unwrap();
        self.buf = buf & (buf - 1); // clear LSB
        self.pos = (self.pos & !(WORD_LEN - 1)) + pos_in_word;
        Some(self.pos)
    }
}
