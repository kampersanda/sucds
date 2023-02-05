//! Rank/select data structure over bit vectors with Vigna's rank9 and hinted selection techniques.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};

use anyhow::Result;

use crate::{bit_vector::Iter, broadword, BitGetter, BitVector, Ranker, Searial, Selector};

const BLOCK_LEN: usize = 8;
const SELECT_ONES_PER_HINT: usize = 64 * BLOCK_LEN * 2;
const SELECT_ZEROS_PER_HINT: usize = SELECT_ONES_PER_HINT;

/// Rank/select data structure over bit vectors with Vigna's rank9 and hinted selection techniques.
///
/// [`RsBitVector`] builds rank/select indexes on a bit vector.
/// For a bit vector of $`n`$ bits,
///
///  - the rank index takes $`0.25n`$ bits, and
///  - the select index takes $`0.03n`$ bits in addition to the space of the rank index.
///
/// This is a yet another Rust port of [succinct::rs_bit_vector](https://github.com/ot/succinct/blob/master/rs_bit_vector.hpp).
///
/// # Examples
///
/// ```
/// use sucds::{RsBitVector, BitGetter, Ranker, Selector};
///
/// let bv = RsBitVector::from_bits([true, false, false, true])
///     .select1_hints()  // To accelerate select1
///     .select0_hints(); // To accelerate select0
///
/// assert_eq!(bv.len(), 4);
///
/// // Need BitGetter
/// assert_eq!(bv.get_bit(1), Some(false));
///
/// // Need Ranker
/// assert_eq!(bv.rank1(1), Some(1));
/// assert_eq!(bv.rank0(1), Some(0));
///
/// // Need Selector
/// assert_eq!(bv.select1(1), Some(3));
/// assert_eq!(bv.select0(0), Some(1));
/// ```
///
/// # References
///
///  - S. Vigna, "Broadword implementation of rank/select queries," In WEA, 2008.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct RsBitVector {
    bv: BitVector,
    block_rank_pairs: Vec<usize>,
    select1_hints: Option<Vec<usize>>,
    select0_hints: Option<Vec<usize>>,
}

impl RsBitVector {
    /// Creates a new vector from input bit vector `bv`.
    pub fn new(bv: BitVector) -> Self {
        Self::build_rank(bv)
    }

    /// Creates a new vector from input bit stream `bits`.
    ///
    /// # Arguments
    ///
    /// - `bits`: Bit stream.
    pub fn from_bits<I>(bits: I) -> Self
    where
        I: IntoIterator<Item = bool>,
    {
        Self::new(BitVector::from_bits(bits))
    }

    /// Builds an index for faster `select1`.
    #[must_use]
    pub fn select1_hints(self) -> Self {
        self.build_select1()
    }

    /// Builds an index for faster `select0`.
    #[must_use]
    pub fn select0_hints(self) -> Self {
        self.build_select0()
    }

    /// Creates an iterator for enumerating bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::RsBitVector;
    ///
    /// let bv = RsBitVector::from_bits([false, true, false]);
    /// let mut it = bv.iter();
    /// assert_eq!(it.next(), Some(false));
    /// assert_eq!(it.next(), Some(true));
    /// assert_eq!(it.next(), Some(false));
    /// assert_eq!(it.next(), None);
    /// ```
    pub const fn iter(&self) -> Iter {
        Iter::new(&self.bv)
    }

    /// Gets the reference of the internal bit vector.
    pub const fn bit_vector(&self) -> &BitVector {
        &self.bv
    }

    /// Gets the number of bits.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.bv.len()
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of bits set.
    #[inline(always)]
    pub fn num_ones(&self) -> usize {
        self.block_rank_pairs[self.block_rank_pairs.len() - 2]
    }

    /// Gets the number of bits unset.
    #[inline(always)]
    pub fn num_zeros(&self) -> usize {
        self.len() - self.num_ones()
    }

    #[inline(always)]
    fn num_blocks(&self) -> usize {
        self.block_rank_pairs.len() / 2 - 1
    }

    #[inline(always)]
    fn block_rank(&self, block: usize) -> usize {
        self.block_rank_pairs[block * 2]
    }

    #[inline(always)]
    fn sub_block_rank(&self, sub_bpos: usize) -> usize {
        let (block, left) = (sub_bpos / BLOCK_LEN, sub_bpos % BLOCK_LEN);
        self.block_rank(block) + (self.sub_block_ranks(block) >> ((7 - left) * 9) & 0x1FF)
    }

    #[inline(always)]
    fn sub_block_ranks(&self, block: usize) -> usize {
        self.block_rank_pairs[block * 2 + 1]
    }

    #[inline(always)]
    fn block_rank0(&self, block: usize) -> usize {
        block * BLOCK_LEN * 64 - self.block_rank(block)
    }

    fn build_rank(bv: BitVector) -> Self {
        let mut next_rank = 0;
        let mut cur_subrank = 0;
        let mut subranks = 0;

        let mut block_rank_pairs = vec![next_rank];

        for i in 0..bv.num_words() {
            let word_pop = broadword::popcount(bv.words()[i]);

            let shift = i % BLOCK_LEN;
            if shift != 0 {
                subranks <<= 9;
                subranks |= cur_subrank;
            }

            next_rank += word_pop;
            cur_subrank += word_pop;

            if shift == BLOCK_LEN - 1 {
                block_rank_pairs.push(subranks);
                block_rank_pairs.push(next_rank);
                subranks = 0;
                cur_subrank = 0;
            }
        }

        let left = BLOCK_LEN - (bv.num_words() % BLOCK_LEN);
        for _ in 0..left {
            subranks <<= 9;
            subranks |= cur_subrank;
        }
        block_rank_pairs.push(subranks);

        if bv.num_words() % BLOCK_LEN != 0 {
            block_rank_pairs.push(next_rank);
            block_rank_pairs.push(0);
        }
        block_rank_pairs.shrink_to_fit();

        Self {
            bv,
            block_rank_pairs,
            select1_hints: None,
            select0_hints: None,
        }
    }

    fn build_select1(mut self) -> Self {
        let mut select1_hints = vec![];
        let mut cur_ones_threshold = SELECT_ONES_PER_HINT;
        for i in 0..self.num_blocks() {
            if self.block_rank(i + 1) > cur_ones_threshold {
                select1_hints.push(i);
                cur_ones_threshold += SELECT_ONES_PER_HINT;
            }
        }
        select1_hints.push(self.num_blocks());
        select1_hints.shrink_to_fit();

        self.select1_hints = Some(select1_hints);
        self
    }

    fn build_select0(mut self) -> Self {
        let mut select0_hints = vec![];
        let mut cur_zeros_threshold = SELECT_ZEROS_PER_HINT;
        for i in 0..self.num_blocks() {
            if self.block_rank0(i + 1) > cur_zeros_threshold {
                select0_hints.push(i);
                cur_zeros_threshold += SELECT_ZEROS_PER_HINT;
            }
        }
        select0_hints.push(self.num_blocks());
        select0_hints.shrink_to_fit();

        self.select0_hints = Some(select0_hints);
        self
    }
}

impl BitGetter for RsBitVector {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{RsBitVector, BitGetter};
    ///
    /// let bv = RsBitVector::from_bits([true, false, false]);
    /// assert_eq!(bv.get_bit(0), Some(true));
    /// assert_eq!(bv.get_bit(1), Some(false));
    /// assert_eq!(bv.get_bit(2), Some(false));
    /// assert_eq!(bv.get_bit(3), None);
    /// ```
    fn get_bit(&self, pos: usize) -> Option<bool> {
        self.bv.get_bit(pos)
    }
}

impl Ranker for RsBitVector {
    /// Returns the number of ones from the zeroth bit to the `pos-1`-th bit, or
    /// [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Ranker, RsBitVector};
    ///
    /// let bv = RsBitVector::from_bits([true, false, false, true]);
    /// assert_eq!(bv.rank1(1), Some(1));
    /// assert_eq!(bv.rank1(2), Some(1));
    /// assert_eq!(bv.rank1(3), Some(1));
    /// assert_eq!(bv.rank1(4), Some(2));
    /// assert_eq!(bv.rank1(5), None);
    /// ```
    fn rank1(&self, pos: usize) -> Option<usize> {
        if self.len() < pos {
            return None;
        }
        if pos == self.len() {
            return Some(self.num_ones());
        }
        let (sub_bpos, sub_left) = (pos / 64, pos % 64);
        let mut r = self.sub_block_rank(sub_bpos);
        if sub_left != 0 {
            r += broadword::popcount(self.bv.words()[sub_bpos] << (64 - sub_left));
        }
        Some(r)
    }

    /// Returns the number of zeros from the zeroth bit to the `pos-1`-th bit, or
    /// [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Ranker, RsBitVector};
    ///
    /// let bv = RsBitVector::from_bits([true, false, false, true]);
    /// assert_eq!(bv.rank0(1), Some(0));
    /// assert_eq!(bv.rank0(2), Some(1));
    /// assert_eq!(bv.rank0(3), Some(2));
    /// assert_eq!(bv.rank0(4), Some(2));
    /// assert_eq!(bv.rank0(5), None);
    /// ```
    fn rank0(&self, pos: usize) -> Option<usize> {
        Some(pos - self.rank1(pos)?)
    }
}

impl Selector for RsBitVector {
    /// Searches the position of the `k`-th bit set.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{RsBitVector, Selector};
    ///
    /// let bv = RsBitVector::from_bits([true, false, false, true]).select1_hints();
    /// assert_eq!(bv.select1(0), Some(0));
    /// assert_eq!(bv.select1(1), Some(3));
    /// assert_eq!(bv.select1(2), None);
    /// ```
    fn select1(&self, k: usize) -> Option<usize> {
        if self.num_ones() <= k {
            return None;
        }

        let block = {
            let (mut a, mut b) = (0, self.num_blocks());
            if let Some(select1_hints) = self.select1_hints.as_ref() {
                let chunk = k / SELECT_ONES_PER_HINT;
                if chunk != 0 {
                    a = select1_hints[chunk - 1];
                }
                b = select1_hints[chunk] + 1;
            }
            while b - a > 1 {
                let mid = a + (b - a) / 2;
                let x = self.block_rank(mid);
                if x <= k {
                    a = mid;
                } else {
                    b = mid;
                }
            }
            a
        };

        debug_assert!(block < self.num_blocks());
        let block_offset = block * BLOCK_LEN;
        let mut cur_rank = self.block_rank(block);
        debug_assert!(cur_rank <= k);

        let rank_in_block_parallel = (k - cur_rank) * broadword::ONES_STEP_9;
        let sub_ranks = self.sub_block_ranks(block);
        let sub_block_offset = broadword::uleq_step_9(sub_ranks, rank_in_block_parallel)
            .wrapping_mul(broadword::ONES_STEP_9)
            >> 54
            & 0x7;
        cur_rank += sub_ranks >> (7 - sub_block_offset).wrapping_mul(9) & 0x1FF;
        debug_assert!(cur_rank <= k);

        let word_offset = block_offset + sub_block_offset;
        let sel = word_offset * 64
            + broadword::select_in_word(self.bv.words()[word_offset], k - cur_rank).unwrap();
        Some(sel)
    }

    /// Searches the position of the `k`-th bit unset.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{RsBitVector, Selector};
    ///
    /// let bv = RsBitVector::from_bits([true, false, false, true]).select0_hints();
    /// assert_eq!(bv.select0(0), Some(1));
    /// assert_eq!(bv.select0(1), Some(2));
    /// assert_eq!(bv.select0(2), None);
    /// ```
    fn select0(&self, k: usize) -> Option<usize> {
        if self.num_zeros() <= k {
            return None;
        }

        let block = {
            let (mut a, mut b) = (0, self.num_blocks());
            if let Some(select0_hints) = self.select0_hints.as_ref() {
                let chunk = k / SELECT_ZEROS_PER_HINT;
                if chunk != 0 {
                    a = select0_hints[chunk - 1];
                }
                b = select0_hints[chunk] + 1;
            }
            while b - a > 1 {
                let mid = a + (b - a) / 2;
                let x = self.block_rank0(mid);
                if x <= k {
                    a = mid;
                } else {
                    b = mid;
                }
            }
            a
        };

        debug_assert!(block < self.num_blocks());
        let block_offset = block * BLOCK_LEN;
        let mut cur_rank = self.block_rank0(block);
        debug_assert!(cur_rank <= k);

        let rank_in_block_parallel = (k - cur_rank) * broadword::ONES_STEP_9;
        let sub_ranks = 64 * broadword::INV_COUNT_STEP_9 - self.sub_block_ranks(block);
        let sub_block_offset = broadword::uleq_step_9(sub_ranks, rank_in_block_parallel)
            .wrapping_mul(broadword::ONES_STEP_9)
            >> 54
            & 0x7;
        cur_rank += sub_ranks >> (7 - sub_block_offset).wrapping_mul(9) & 0x1FF;
        debug_assert!(cur_rank <= k);

        let word_offset = block_offset + sub_block_offset;
        let sel = word_offset * 64
            + broadword::select_in_word(!self.bv.words()[word_offset], k - cur_rank).unwrap();
        Some(sel)
    }
}

impl Searial for RsBitVector {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = self.bv.serialize_into(&mut writer)?;
        mem += self.block_rank_pairs.serialize_into(&mut writer)?;
        mem += self.select1_hints.serialize_into(&mut writer)?;
        mem += self.select0_hints.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let bv = BitVector::deserialize_from(&mut reader)?;
        let block_rank_pairs = Vec::<usize>::deserialize_from(&mut reader)?;
        let select1_hints = Option::<Vec<usize>>::deserialize_from(&mut reader)?;
        let select0_hints = Option::<Vec<usize>>::deserialize_from(&mut reader)?;
        Ok(Self {
            bv,
            block_rank_pairs,
            select1_hints,
            select0_hints,
        })
    }

    fn size_in_bytes(&self) -> usize {
        self.bv.size_in_bytes()
            + self.block_rank_pairs.size_in_bytes()
            + self.select1_hints.size_in_bytes()
            + self.select0_hints.size_in_bytes()
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

    fn test_rank_select1(bits: &[bool], bv: &RsBitVector) {
        let mut cur_rank = 0;
        for i in 0..bits.len() {
            assert_eq!(bv.rank1(i), Some(cur_rank));
            if bits[i] {
                assert_eq!(bv.select1(cur_rank), Some(i));
                cur_rank += 1;
            }
        }
        assert_eq!(cur_rank, bv.num_ones());
    }

    fn test_rank_select0(bits: &[bool], bv: &RsBitVector) {
        let mut cur_rank = 0;
        for i in 0..bits.len() {
            assert_eq!(bv.rank0(i), Some(cur_rank));
            if !bits[i] {
                assert_eq!(bv.select0(cur_rank), Some(i));
                cur_rank += 1;
            }
        }
        assert_eq!(cur_rank, bv.num_zeros());
    }

    #[test]
    fn test_random_bits() {
        for seed in 0..100 {
            let bits = gen_random_bits(10000, seed);
            let bv = RsBitVector::from_bits(bits.iter().cloned())
                .select1_hints()
                .select0_hints();
            test_rank_select1(&bits, &bv);
            test_rank_select0(&bits, &bv);
        }
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let bv = RsBitVector::from_bits(gen_random_bits(10000, 42))
            .select1_hints()
            .select0_hints();
        let size = bv.serialize_into(&mut bytes).unwrap();
        let other = RsBitVector::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(bv, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, bv.size_in_bytes());
    }
}
