//! Updatable bit vector in a plain format, supporting some utilities such as chunking and predecessor queries.
pub mod unary;

use std::io::{Read, Write};

use anyhow::{anyhow, Result};

use crate::bit_vectors::prelude::*;
use crate::broadword;
use crate::utils::MatrixView;
use crate::Serializable;
use unary::UnaryIter;

/// The number of bits in a machine word.
pub const WORD_LEN: usize = std::mem::size_of::<usize>() * 8;

/// Updatable bit vector in a plain format, supporting some utilities such as chunking and predecessor queries.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use sucds::bit_vectors::BitVector;
///
/// let mut bv = BitVector::new();
/// bv.push_bit(true);
/// bv.push_bit(false);
///
/// assert_eq!(bv.len(), 2);
/// assert_eq!(bv.get_bit(0), Some(true));
///
/// bv.set_bit(0, false)?;
/// assert_eq!(bv.get_bit(0), Some(false));
/// # Ok(())
/// # }
/// ```
///
/// # Credits
///
/// This is a yet another Rust port of [succinct::bit_vector](https://github.com/ot/succinct/blob/master/bit_vector.hpp).
#[derive(Default, Clone, PartialEq, Eq)]
pub struct BitVector {
    words: Vec<u64>,
    len: usize,
}

impl BitVector {
    /// Creates a new empty vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::new();
    /// assert_eq!(bv.len(), 0);
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new vector that at least `capa` bits are reserved.
    ///
    /// # Arguments
    ///
    ///  - `capa`: Number of elements reserved at least.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::with_capacity(40);
    /// assert_eq!(bv.len(), 0);
    /// assert_eq!(bv.capacity(), 64);
    /// ```
    pub fn with_capacity(capa: usize) -> Self {
        Self {
            words: Vec::with_capacity(Self::words_for(capa)),
            len: 0,
        }
    }

    /// Creates a new vector that stores `len` bits,
    /// where each bit is initialized by `bit`.
    ///
    /// # Arguments
    ///
    ///  - `bit`: Bit value used for intinialization.
    ///  - `len`: Number of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bit(false, 5);
    /// assert_eq!(bv.len(), 5);
    /// assert_eq!(bv.get_bit(0), Some(false));
    /// ```
    pub fn from_bit(bit: bool, len: usize) -> Self {
        let word = if bit { u64::MAX } else { 0 };
        let mut words = vec![word; Self::words_for(len)];
        let shift = len % WORD_LEN;
        if shift != 0 {
            let mask = (1 << shift) - 1;
            *words.last_mut().unwrap() &= mask;
        }
        Self { words, len }
    }

    /// Creates a new vector from input bit stream `bits`.
    ///
    /// # Arguments
    ///
    ///  - `bits`: Bit stream.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([false, true, false]);
    /// assert_eq!(bv.len(), 3);
    /// assert_eq!(bv.get_bit(1), Some(true));
    /// ```
    pub fn from_bits<I>(bits: I) -> Self
    where
        I: IntoIterator<Item = bool>,
    {
        let mut this = Self::new();
        bits.into_iter().for_each(|b| this.push_bit(b));
        this
    }

    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    ///
    /// # Arguments
    ///
    ///  - `pos`: Bit position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([true, false, false]);
    /// assert_eq!(bv.get_bit(0), Some(true));
    /// assert_eq!(bv.get_bit(1), Some(false));
    /// assert_eq!(bv.get_bit(2), Some(false));
    /// assert_eq!(bv.get_bit(3), None);
    /// ```
    pub fn get_bit(&self, pos: usize) -> Option<bool> {
        if pos < self.len {
            let (block, shift) = (pos / WORD_LEN, pos % WORD_LEN);
            Some((self.words[block] >> shift) & 1 == 1)
        } else {
            None
        }
    }

    /// Updates the `pos`-th bit to `bit`.
    ///
    /// # Arguments
    ///
    ///  - `pos`: Bit position.
    ///  - `bit`: Bit value set.
    ///
    /// # Errors
    ///
    /// An error is returned if `self.len() <= pos`.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let mut bv = BitVector::from_bits([false, true, false]);
    /// bv.set_bit(1, false)?;
    /// assert_eq!(bv.get_bit(1), Some(false));
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn set_bit(&mut self, pos: usize, bit: bool) -> Result<()> {
        if self.len() <= pos {
            return Err(anyhow!(
                "pos must be no greater than self.len()={}, but got {pos}.",
                self.len()
            ));
        }
        let word = pos / WORD_LEN;
        let pos_in_word = pos % WORD_LEN;
        self.words[word] &= !(1 << pos_in_word);
        self.words[word] |= (bit as u64) << pos_in_word;
        Ok(())
    }

    /// Pushes `bit` at the end.
    ///
    /// # Arguments
    ///
    ///  - `bit`: Bit value pushed.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_bit(true);
    /// bv.push_bit(false);
    /// assert_eq!(bv.len(), 2);
    /// ```
    #[inline(always)]
    pub fn push_bit(&mut self, bit: bool) {
        let pos_in_word = self.len % WORD_LEN;
        if pos_in_word == 0 {
            self.words.push(bit as u64);
        } else {
            let cur_word = self.words.last_mut().unwrap();
            *cur_word |= (bit as u64) << pos_in_word;
        }
        self.len += 1;
    }

    /// Returns the `len` bits starting at the `pos`-th bit, or [`None`] if
    ///
    ///  - `len` is greater than [`WORD_LEN`], or
    ///  - `self.len() < pos + len`.
    ///
    /// # Arguments
    ///
    ///  - `pos`: Bit position.
    ///  - `len`: Number of bits extracted.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([true, false, true, false]);
    /// assert_eq!(bv.get_bits(1, 2), Some(0b10));
    /// assert_eq!(bv.get_bits(2, 3), None);
    /// ```
    #[inline(always)]
    pub fn get_bits(&self, pos: usize, len: usize) -> Option<u64> {
        if WORD_LEN < len || self.len() < pos + len {
            return None;
        }
        if len == 0 {
            return Some(0);
        }
        let (block, shift) = (pos / WORD_LEN, pos % WORD_LEN);
        let mask = {
            if len < WORD_LEN {
                (1 << len) - 1
            } else {
                u64::MAX
            }
        };
        let bits = if shift + len <= WORD_LEN {
            (self.words[block] >> shift) & mask
        } else {
            (self.words[block] >> shift) | ((self.words[block + 1] << (WORD_LEN - shift)) & mask)
        };
        Some(bits)
    }

    /// Updates the `len` bits starting at the `pos`-th bit to `bits`.
    ///
    /// # Arguments
    ///
    ///  - `pos`: Bit position.
    ///  - `bits`: Bit chunk set.
    ///  - `len`: Number of bits of the chunk.
    ///
    /// # Errors
    ///
    /// An error is returned if
    ///
    ///  - `len` is greater than [`WORD_LEN`], or
    ///  - `self.len() < pos + len`.
    ///
    /// # Notes
    ///
    /// If `bits` has active bits other than the lowest `len` bits,
    /// these will be trancated automatically.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let mut bv = BitVector::from_bit(false, 4);
    /// bv.set_bits(1, 0b11, 2)?;
    /// assert_eq!(bv.get_bits(0, 4), Some(0b0110));
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn set_bits(&mut self, pos: usize, bits: u64, len: usize) -> Result<()> {
        if WORD_LEN < len {
            return Err(anyhow!(
                "len must be no greater than {WORD_LEN}, but got {len}."
            ));
        }
        if self.len() < pos + len {
            return Err(anyhow!(
                "pos+len must be no greater than self.len()={}, but got {}.",
                self.len(),
                pos + len
            ));
        }
        if len == 0 {
            return Ok(());
        }
        let mask = {
            if len < WORD_LEN {
                (1 << len) - 1
            } else {
                u64::MAX
            }
        };
        let bits = bits & mask;

        let word = pos / WORD_LEN;
        let pos_in_word = pos % WORD_LEN;

        self.words[word] &= !(mask << pos_in_word);
        self.words[word] |= bits << pos_in_word;

        let stored = WORD_LEN - pos_in_word;
        if stored < len {
            self.words[word + 1] &= !(mask >> stored);
            self.words[word + 1] |= bits >> stored;
        }
        Ok(())
    }

    /// Pushes `bits` of `len` bits at the end.
    ///
    /// # Arguments
    ///
    ///  - `bits`: Bit chunk set.
    ///  - `len`: Number of bits of the chunk.
    ///
    /// # Errors
    ///
    /// It will return an error if
    ///
    /// - `len` is greater than [`WORD_LEN`].
    ///
    /// # Notes
    ///
    /// If `bits` has active bits other than the lowest `len` bits,
    /// these will be trancated automatically.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_bits(0b11, 2)?;
    /// bv.push_bits(0b101, 3)?;
    /// assert_eq!(bv.get_bits(0, 5), Some(0b10111));
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn push_bits(&mut self, bits: u64, len: usize) -> Result<()> {
        if WORD_LEN < len {
            return Err(anyhow!(
                "len must be no greater than {WORD_LEN}, but got {len}."
            ));
        }
        if len == 0 {
            return Ok(());
        }

        let mask = {
            if len < WORD_LEN {
                (1 << len) - 1
            } else {
                u64::MAX
            }
        };
        let bits = bits & mask;

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
        Ok(())
    }

    /// Returns the largest bit position `pred` such that `pred <= pos` and the `pred`-th bit is set, or
    /// [`None`] if not found or `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Linear
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([false, true, false, true]);
    /// assert_eq!(bv.predecessor1(3), Some(3));
    /// assert_eq!(bv.predecessor1(2), Some(1));
    /// assert_eq!(bv.predecessor1(1), Some(1));
    /// assert_eq!(bv.predecessor1(0), None);
    /// ```
    pub fn predecessor1(&self, pos: usize) -> Option<u64> {
        if self.len() <= pos {
            return None;
        }
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

    /// Returns the largest bit position `pred` such that `pred <= pos` and the `pred`-th bit is unset, or
    /// [`None`] if not found or `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Linear
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([true, false, true, false]);
    /// assert_eq!(bv.predecessor0(3), Some(3));
    /// assert_eq!(bv.predecessor0(2), Some(1));
    /// assert_eq!(bv.predecessor0(1), Some(1));
    /// assert_eq!(bv.predecessor0(0), None);
    /// ```
    pub fn predecessor0(&self, pos: usize) -> Option<u64> {
        if self.len() <= pos {
            return None;
        }
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

    /// Returns the smallest bit position `succ` such that `succ >= pos` and the `succ`-th bit is set, or
    /// [`None`] if not found or `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Linear
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([true, false, true, false]);
    /// assert_eq!(bv.successor1(0), Some(0));
    /// assert_eq!(bv.successor1(1), Some(2));
    /// assert_eq!(bv.successor1(2), Some(2));
    /// assert_eq!(bv.successor1(3), None);
    /// ```
    pub fn successor1(&self, pos: usize) -> Option<u64> {
        if self.len() <= pos {
            return None;
        }
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

    /// Returns the smallest bit position `succ` such that `succ >= pos` and the `succ`-th bit is unset, or
    /// [`None`] if not found or `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Linear
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([false, true, false, true]);
    /// assert_eq!(bv.successor0(0), Some(0));
    /// assert_eq!(bv.successor0(1), Some(2));
    /// assert_eq!(bv.successor0(2), Some(2));
    /// assert_eq!(bv.successor0(3), None);
    /// ```
    pub fn successor0(&self, pos: usize) -> Option<u64> {
        if self.len() <= pos {
            return None;
        }
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

    /// Creates an iterator for enumerating bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([false, true, false]);
    /// let mut it = bv.iter();
    /// assert_eq!(it.next(), Some(false));
    /// assert_eq!(it.next(), Some(true));
    /// assert_eq!(it.next(), Some(false));
    /// assert_eq!(it.next(), None);
    /// ```
    pub const fn iter(&self) -> Iter {
        Iter::new(self)
    }

    /// Creates an iterator for enumerating positions of set bits, starting at bit position `pos`.
    ///
    /// # Arguments
    ///
    ///  - `pos`: Bit position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([true, true, false, true]);
    /// let mut it = bv.unary_iter(1);
    /// assert_eq!(it.next(), Some(1));
    /// assert_eq!(it.next(), Some(3));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn unary_iter(&self, pos: usize) -> UnaryIter {
        UnaryIter::new(self, pos)
    }

    /// Returns `self.get_bits(pos, 64)` but it can extend further `self.len()`,
    /// padding with zeros. If `self.len() <= pos`, [`None`] is returned.
    ///
    /// # Arguments
    ///
    ///  - `pos`: Bit position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::BitVector;
    ///
    /// let bv = BitVector::from_bits([true, false, true, false]);
    /// assert_eq!(bv.get_word64(1), Some(0b10));
    /// assert_eq!(bv.get_bits(1, 64), None);  // out of bounds
    /// ```
    #[inline(always)]
    pub fn get_word64(&self, pos: usize) -> Option<u64> {
        if self.len <= pos {
            return None;
        }
        let (block, shift) = (pos / WORD_LEN, pos % WORD_LEN);
        let mut word = self.words[block] >> shift;
        if shift != 0 && block + 1 < self.words.len() {
            word |= self.words[block + 1] << (64 - shift);
        }
        Some(word)
    }

    /// Returns the number of bits stored.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Checks if the vector is empty.
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the slice of raw words.
    pub fn words(&self) -> &[usize] {
        &self.words
    }

    /// Converts into the slice of raw words.
    pub fn into_words(self) -> Vec<usize> {
        self.words
    }

    /// Returns the total number of bits it can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.words.capacity() * WORD_LEN
    }

    /// Gets the number of words.
    #[inline(always)]
    pub fn num_words(&self) -> usize {
        self.words.len()
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

impl Build for BitVector {
    /// Creates a new vector from input bit stream `bits`.
    ///
    /// # Arguments
    ///
    /// - `bits`: Bit stream.
    /// - `with_rank`: Dummy.
    /// - `with_select1`: Dummy.
    /// - `with_select0`: Dummy.
    ///
    /// # Errors
    ///
    /// Never.
    fn build_from_bits<I>(
        bits: I,
        _with_rank: bool,
        _with_select1: bool,
        _with_select0: bool,
    ) -> Result<Self>
    where
        I: IntoIterator<Item = bool>,
        Self: Sized,
    {
        Ok(Self::from_bits(bits))
    }
}

impl NumBits for BitVector {
    /// Returns the number of bits stored (just wrapping [`Self::len()`]).
    fn num_bits(&self) -> usize {
        self.len()
    }

    /// Returns the number of bits set.
    ///
    /// # Notes on complexity
    ///
    /// It is performed by linear scan in $`O(u)`$ time.
    fn num_ones(&self) -> usize {
        self.rank1(self.len).unwrap()
    }
}

impl Access for BitVector {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    ///
    /// # Arguments
    ///
    ///  - `pos`: Bit position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, Access};
    ///
    /// let bv = BitVector::from_bits([true, false, false]);
    /// assert_eq!(bv.access(0), Some(true));
    /// assert_eq!(bv.access(1), Some(false));
    /// assert_eq!(bv.access(2), Some(false));
    /// assert_eq!(bv.access(3), None);
    /// ```
    fn access(&self, pos: usize) -> Option<bool> {
        if pos < self.len {
            let (block, shift) = (pos / WORD_LEN, pos % WORD_LEN);
            Some((self.words[block] >> shift) & 1 == 1)
        } else {
            None
        }
    }
}

impl Rank for BitVector {
    /// Returns the number of ones from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `self.len() < pos`.
    ///
    /// # Complexity
    ///
    /// - Linear
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, Rank};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// assert_eq!(bv.rank1(1), Some(1));
    /// assert_eq!(bv.rank1(2), Some(1));
    /// assert_eq!(bv.rank1(3), Some(1));
    /// assert_eq!(bv.rank1(4), Some(2));
    /// assert_eq!(bv.rank1(5), None);
    /// ```
    fn rank1(&self, pos: usize) -> Option<u64> {
        if self.len() < pos {
            return None;
        }
        let mut r = 0;
        let (wpos, left) = (pos / WORD_LEN, pos % WORD_LEN);
        for &w in &self.words[..wpos] {
            r += broadword::popcount(w);
        }
        if left != 0 {
            r += broadword::popcount(self.words[wpos] << (WORD_LEN - left));
        }
        Some(r)
    }

    /// Returns the number of zeros from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `self.len() < pos`.
    ///
    /// # Complexity
    ///
    /// - Linear
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, Rank};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// assert_eq!(bv.rank0(1), Some(0));
    /// assert_eq!(bv.rank0(2), Some(1));
    /// assert_eq!(bv.rank0(3), Some(2));
    /// assert_eq!(bv.rank0(4), Some(2));
    /// assert_eq!(bv.rank0(5), None);
    /// ```
    fn rank0(&self, pos: usize) -> Option<u64> {
        Some(pos - self.rank1(pos)?)
    }
}

impl Select for BitVector {
    /// Searches the position of the `k`-th bit set, or
    /// [`None`] if `k` is no less than the number of ones.
    ///
    /// # Complexity
    ///
    /// - Linear
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, Select};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// assert_eq!(bv.select1(0), Some(0));
    /// assert_eq!(bv.select1(1), Some(3));
    /// assert_eq!(bv.select1(2), None);
    /// ```
    fn select1(&self, k: usize) -> Option<u64> {
        let mut wpos = 0;
        let mut cur_rank = 0;
        while wpos < self.words.len() {
            let cnt = broadword::popcount(self.words[wpos]);
            if k < cur_rank + cnt {
                break;
            }
            wpos += 1;
            cur_rank += cnt;
        }
        if wpos == self.words.len() {
            return None;
        }
        let sel =
            wpos * WORD_LEN + broadword::select_in_word(self.words[wpos], k - cur_rank).unwrap();
        Some(sel)
    }

    /// Searches the position of the `k`-th bit unset, or
    /// [`None`] if `k` is no less than the number of zeros.
    ///
    /// # Complexity
    ///
    /// - Linear
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, Select};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// assert_eq!(bv.select0(0), Some(1));
    /// assert_eq!(bv.select0(1), Some(2));
    /// assert_eq!(bv.select0(2), None);
    /// ```
    fn select0(&self, k: usize) -> Option<u64> {
        let mut wpos = 0;
        let mut cur_rank = 0;
        while wpos < self.words.len() {
            let cnt = broadword::popcount(!self.words[wpos]);
            if k < cur_rank + cnt {
                break;
            }
            wpos += 1;
            cur_rank += cnt;
        }
        if wpos == self.words.len() {
            return None;
        }
        let sel =
            wpos * WORD_LEN + broadword::select_in_word(!self.words[wpos], k - cur_rank).unwrap();
        // NOTE(kampersanda): sel can be no less than self.len() because overflowed bits are
        // initialized by zero and can be considered by select0.
        (sel < self.len()).then(|| sel)
    }
}

/// Iterator for enumerating bits, created by [`BitVector::iter()`].
pub struct Iter<'a> {
    bv: &'a BitVector,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(bv: &'a BitVector) -> Self {
        Self { bv, pos: 0 }
    }
}

impl Iterator for Iter<'_> {
    type Item = bool;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.bv.len() {
            let x = self.bv.access(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<u64>) {
        (self.bv.len(), Some(self.bv.len()))
    }
}

impl std::iter::Extend<bool> for BitVector {
    fn extend<I>(&mut self, bits: I)
    where
        I: IntoIterator<Item = bool>,
    {
        bits.into_iter().for_each(|b| self.push_bit(b));
    }
}

impl std::fmt::Debug for BitVector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut bits = vec![0u8; self.len()];
        for (i, b) in bits.iter_mut().enumerate() {
            *b = self.access(i).unwrap() as u8;
        }
        f.debug_struct("BitVector")
            .field("bits", &MatrixView::new(&bits, 16))
            .field("len", &self.len)
            .finish()
    }
}

impl Serializable for BitVector {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = self.words.serialize_into(&mut writer)?;
        mem += self.len.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let words = Vec::<usize>::deserialize_from(&mut reader)?;
        let len = usize::deserialize_from(&mut reader)?;
        Ok(Self { words, len })
    }

    fn size_in_bytes(&self) -> usize {
        self.words.size_in_bytes() + usize::size_of().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_bit_oob() {
        let mut bv = BitVector::from_bit(false, 3);
        let e = bv.set_bit(3, true);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("pos must be no greater than self.len()=3, but got 3.".to_string())
        );
    }

    #[test]
    fn test_set_bits_over_word() {
        let mut bv = BitVector::from_bit(false, 100);
        let e = bv.set_bits(0, 0b0, 65);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("len must be no greater than 64, but got 65.".to_string())
        );
    }

    #[test]
    fn test_set_bits_oob() {
        let mut bv = BitVector::from_bit(false, 3);
        let e = bv.set_bits(2, 0b11, 2);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("pos+len must be no greater than self.len()=3, but got 4.".to_string())
        );
    }

    #[test]
    fn test_set_bits_truncation() {
        let mut bv = BitVector::from_bit(false, 3);
        bv.set_bits(0, 0b111, 2).unwrap();
        assert_eq!(bv, BitVector::from_bits([true, true, false]));
    }

    #[test]
    fn test_set_bits_accross_word() {
        let mut bv = BitVector::from_bit(false, 100);
        bv.set_bits(62, 0b11111, 5).unwrap();
        assert_eq!(bv.get_bits(61, 7).unwrap(), 0b0111110);
    }

    #[test]
    fn test_push_bits_over_word() {
        let mut bv = BitVector::new();
        let e = bv.push_bits(0b0, 65);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("len must be no greater than 64, but got 65.".to_string())
        );
    }

    #[test]
    fn test_push_bits_truncation() {
        let mut bv = BitVector::new();
        bv.push_bits(0b111, 2).unwrap();
        assert_eq!(bv, BitVector::from_bits([true, true]));
    }

    #[test]
    fn test_push_bits_accross_word() {
        let mut bv = BitVector::from_bit(false, 62);
        bv.push_bits(0b011111, 6).unwrap();
        assert_eq!(bv.get_bits(61, 7).unwrap(), 0b0111110);
    }

    #[test]
    fn test_get_word64_oob() {
        let bv = BitVector::from_bit(false, 3);
        assert_eq!(bv.get_word64(3), None);
    }

    #[test]
    fn test_get_word64_overflow() {
        // Test a case that can see the next block (but not exist).
        let bv = BitVector::from_bit(true, 64);
        assert_eq!(bv.get_word64(60), Some(0b1111));
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let bv = BitVector::from_bits([false, true, false, false, true]);
        let size = bv.serialize_into(&mut bytes).unwrap();
        let other = BitVector::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(bv, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, bv.size_in_bytes());
    }
}
