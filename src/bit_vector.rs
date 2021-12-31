pub mod unary;

use std::io::{Read, Write};
use std::mem::size_of;

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use crate::bit_vector::unary::UnaryIterator;
use crate::{broadword, util};

pub(crate) const WORD_LEN: usize = std::mem::size_of::<usize>() * 8;

/// Bit vector in a plain format, supporting some utilities such as update, chunking, and predecessor queries.
///
/// This is a yet another Rust port of [succinct::bit_vector](https://github.com/ot/succinct/blob/master/bit_vector.hpp).
///
/// # Examples
///
/// ```
/// use sucds::BitVector;
///
/// let bv = BitVector::from_bits(&[true, false, false, true]);
///
/// assert_eq!(bv.get_bit(0), true);
/// assert_eq!(bv.get_bit(1), false);
/// assert_eq!(bv.get_bit(2), false);
/// assert_eq!(bv.get_bit(3), true);
///
/// assert_eq!(bv.predecessor1(2), Some(0));
/// assert_eq!(bv.predecessor0(2), Some(2));
/// assert_eq!(bv.successor1(1), Some(3));
/// assert_eq!(bv.successor0(1), Some(1));
///
/// let mut bytes = vec![];
/// let size = bv.serialize_into(&mut bytes).unwrap();
/// let other = BitVector::deserialize_from(&bytes[..]).unwrap();
/// assert_eq!(bv, other);
/// assert_eq!(size, bytes.len());
/// assert_eq!(size, bv.size_in_bytes());
/// ```
#[derive(Default, PartialEq, Eq)]
pub struct BitVector {
    words: Vec<usize>,
    len: usize,
}

impl BitVector {
    /// Creates a new empty [`BitVector`].
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new [`BitVector`] of `len` bits.
    pub fn with_len(len: usize) -> Self {
        Self {
            words: vec![0; Self::words_for(len)],
            len,
        }
    }

    /// Creates a new [`BitVector`] that `capa` bits are reserved.
    pub fn with_capacity(capa: usize) -> Self {
        Self {
            words: Vec::with_capacity(Self::words_for(capa)),
            len: 0,
        }
    }

    /// Serializes the data structure into the writer,
    /// returning the number of serialized bytes.
    ///
    /// # Arguments
    ///
    /// - `writer`: `std::io::Write` variable.
    pub fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mem = util::int_vector::serialize_into(&self.words, &mut writer)?;
        writer.write_u64::<LittleEndian>(self.len as u64)?;
        Ok(mem + size_of::<u64>())
    }

    /// Deserializes the data structure from the reader.
    ///
    /// # Arguments
    ///
    /// - `reader`: `std::io::Read` variable.
    pub fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let words = util::int_vector::deserialize_from(&mut reader)?;
        let len = reader.read_u64::<LittleEndian>()? as usize;
        Ok(Self { words, len })
    }

    /// Returns the number of bytes to serialize the data structure.
    pub fn size_in_bytes(&self) -> usize {
        util::int_vector::size_in_bytes(&self.words) + size_of::<u64>()
    }

    /// Creates a new [`BitVector`] from input bitset `bits`.
    ///
    /// # Arguments
    ///
    /// - `bits`: List of bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let bv = BitVector::from_bits(&[true, false, false, true]);
    /// assert_eq!(bv.get_bit(0), true);
    /// assert_eq!(bv.get_bit(1), false);
    /// assert_eq!(bv.get_bit(2), false);
    /// assert_eq!(bv.get_bit(3), true);
    /// ```
    pub fn from_bits<'a, I>(bits: I) -> Self
    where
        I: IntoIterator<Item = &'a bool>,
    {
        let mut this = Self::new();
        bits.into_iter().for_each(|&b| this.push_bit(b));
        this
    }

    /// Gets the `pos`-th bit.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let bv = BitVector::from_bits(&[true, false, false, true]);
    /// assert_eq!(bv.get_bit(0), true);
    /// assert_eq!(bv.get_bit(1), false);
    /// assert_eq!(bv.get_bit(2), false);
    /// assert_eq!(bv.get_bit(3), true);
    /// ```
    #[inline(always)]
    pub fn get_bit(&self, pos: usize) -> bool {
        debug_assert!(pos < self.len);
        let (block, shift) = (pos / WORD_LEN, pos % WORD_LEN);
        (self.words[block] >> shift) & 1 == 1
    }

    /// Sets the `pos`-th bit to `bit`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    /// - `bit`: Set bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let mut bv = BitVector::from_bits(&[false, true, true, false]);
    /// bv.set_bit(0, true);
    /// bv.set_bit(2, false);
    /// assert_eq!(bv.get_bit(0), true);
    /// assert_eq!(bv.get_bit(1), true);
    /// assert_eq!(bv.get_bit(2), false);
    /// assert_eq!(bv.get_bit(3), false);
    /// ```
    #[inline(always)]
    pub fn set_bit(&mut self, pos: usize, bit: bool) {
        debug_assert!(pos < self.len);
        let word = pos / WORD_LEN;
        let pos_in_word = pos % WORD_LEN;
        self.words[word] &= !(1 << pos_in_word);
        self.words[word] |= (bit as usize) << pos_in_word;
    }

    /// Pushes `bit` at the end.
    ///
    /// # Arguments
    ///
    /// - `bit`: Pushed bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_bit(true);
    /// bv.push_bit(false);
    /// assert_eq!(bv.get_bit(0), true);
    /// assert_eq!(bv.get_bit(1), false);
    /// ```
    #[inline(always)]
    pub fn push_bit(&mut self, bit: bool) {
        let pos_in_word = self.len % WORD_LEN;
        if pos_in_word == 0 {
            self.words.push(bit as usize);
        } else {
            let cur_word = self.words.last_mut().unwrap();
            *cur_word |= (bit as usize) << pos_in_word;
        }
        self.len += 1;
    }

    /// Gets the `len` bits starting at the `pos`-th bit.
    ///
    /// # Arguments
    ///
    /// - `pos`: Starting bit position.
    /// - `len`: Number of bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let bv = BitVector::from_bits(&[true, false, true, false, true]);
    /// assert_eq!(bv.get_bits(1, 4), 0b1010);
    /// ```
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

    /// Sets the `len` bits starting at the `pos`-th bit to `bits`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Starting bit position.
    /// - `bits`: Set bits.
    /// - `len`: Number of bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let mut bv = BitVector::with_len(5);
    /// bv.set_bits(1, 0b1010, 4);
    /// assert_eq!(bv.get_bits(1, 4), 0b1010);
    /// ```
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

    /// Pushes `bits` of `len` bits at the end.
    ///
    /// # Arguments
    ///
    /// - `bits`: Pushed bits.
    /// - `len`: Number of bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_bits(0b1, 1);
    /// bv.push_bits(0b1010, 4);
    /// assert_eq!(bv.get_bits(1, 4), 0b1010);
    /// ```
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
            if len > WORD_LEN - pos_in_word {
                self.words.push(bits >> (WORD_LEN - pos_in_word));
            }
        }
        self.len += len;
    }

    /// Gets the largest bit position `pred` such that `pred <= pos` and the `pred`-th bit is set.
    /// If not found, `None` is returned.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let bv = BitVector::from_bits(&[false, true, false, true]);
    /// assert_eq!(bv.predecessor1(3), Some(3));
    /// assert_eq!(bv.predecessor1(2), Some(1));
    /// assert_eq!(bv.predecessor1(1), Some(1));
    /// assert_eq!(bv.predecessor1(0), None);
    /// ```
    #[inline(always)]
    pub fn predecessor1(&self, pos: usize) -> Option<usize> {
        debug_assert!(pos < self.len());
        let mut block = pos / WORD_LEN;
        let shift = WORD_LEN - pos % WORD_LEN - 1;
        let mut word = (self.words[block] << shift) >> shift;
        loop {
            if let Some(ret) = broadword::msb(word) {
                return Some(block * WORD_LEN + ret);
            } else if block == 0 {
                return None;
            }
            block -= 1;
            word = self.words[block];
        }
    }

    /// Gets the smallest bit position `succ` such that `succ >= pos` and the `succ`-th bit is set.
    /// If not found, `None` is returned.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let bv = BitVector::from_bits(&[true, false, true, false]);
    /// assert_eq!(bv.successor1(0), Some(0));
    /// assert_eq!(bv.successor1(1), Some(2));
    /// assert_eq!(bv.successor1(2), Some(2));
    /// assert_eq!(bv.successor1(3), None);
    /// ```
    #[inline(always)]
    pub fn successor1(&self, pos: usize) -> Option<usize> {
        debug_assert!(pos < self.len());
        let mut block = pos / WORD_LEN;
        let shift = pos % WORD_LEN;
        let mut word = (self.words[block] >> shift) << shift;
        loop {
            if let Some(ret) = broadword::lsb(word) {
                return Some(block * WORD_LEN + ret).filter(|&i| i < self.len());
            }
            block += 1;
            if block == self.words.len() {
                return None;
            }
            word = self.words[block];
        }
    }

    /// Gets the largest bit position `pred` such that `pred <= pos` and the `pred`-th bit is not set.
    /// If not found, `None` is returned.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let bv = BitVector::from_bits(&[true, false, true, false]);
    /// assert_eq!(bv.predecessor0(3), Some(3));
    /// assert_eq!(bv.predecessor0(2), Some(1));
    /// assert_eq!(bv.predecessor0(1), Some(1));
    /// assert_eq!(bv.predecessor0(0), None);
    /// ```
    #[inline(always)]
    pub fn predecessor0(&self, pos: usize) -> Option<usize> {
        debug_assert!(pos < self.len());
        let mut block = pos / WORD_LEN;
        let shift = WORD_LEN - pos % WORD_LEN - 1;
        let mut word = (!self.words[block] << shift) >> shift;
        loop {
            if let Some(ret) = broadword::msb(word) {
                return Some(block * WORD_LEN + ret);
            } else if block == 0 {
                return None;
            }
            block -= 1;
            word = !self.words[block];
        }
    }

    /// Gets the smallest bit position `succ` such that `succ >= pos` and the `succ`-th bit is not set.
    /// If not found, `None` is returned.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let bv = BitVector::from_bits(&[false, true, false, true]);
    /// assert_eq!(bv.successor0(0), Some(0));
    /// assert_eq!(bv.successor0(1), Some(2));
    /// assert_eq!(bv.successor0(2), Some(2));
    /// assert_eq!(bv.successor0(3), None);
    /// ```
    #[inline(always)]
    pub fn successor0(&self, pos: usize) -> Option<usize> {
        debug_assert!(pos < self.len());
        let mut block = pos / WORD_LEN;
        let shift = pos % WORD_LEN;
        let mut word = (!self.words[block] >> shift) << shift;
        loop {
            if let Some(ret) = broadword::lsb(word) {
                return Some(block * WORD_LEN + ret).filter(|&i| i < self.len());
            }
            block += 1;
            if block == self.words.len() {
                return None;
            }
            word = !self.words[block];
        }
    }

    pub fn unary_iter(&self, pos: usize) -> UnaryIterator {
        UnaryIterator::new(self, pos)
    }

    /// Gets the `word_pos`-th word.
    #[inline(always)]
    pub fn get_word(&self, word_pos: usize) -> usize {
        self.words[word_pos]
    }

    /// Gets the number of words.
    #[inline(always)]
    pub fn num_words(&self) -> usize {
        self.words.len()
    }

    /// Gets the number of bits.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Shrinks the capacity of the vector as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.words.shrink_to_fit();
    }

    #[inline(always)]
    const fn words_for(n: usize) -> usize {
        (n + WORD_LEN - 1) / WORD_LEN
    }
}

impl std::fmt::Debug for BitVector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut bits = vec![0u8; self.len()];
        for (i, b) in bits.iter_mut().enumerate() {
            *b = self.get_bit(i) as u8;
        }
        f.debug_struct("BitVector")
            .field("bits", &bits)
            .field("len", &self.len)
            .finish()
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
        let mut bytes = vec![];
        let bv = BitVector::from_bits(&gen_random_bits(10000, 42));
        let size = bv.serialize_into(&mut bytes).unwrap();
        let other = BitVector::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(bv, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, bv.size_in_bytes());
    }
}
