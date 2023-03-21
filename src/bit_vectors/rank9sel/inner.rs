//! Internal index structure of [`Rank9Sel`](crate::Rank9Sel).
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};

use anyhow::Result;

use crate::bit_vectors::BitVector;
use crate::bit_vectors::BitVectorStat;
use crate::{broadword, Serializable};

const BLOCK_LEN: usize = 8;
const SELECT_ONES_PER_HINT: usize = 64 * BLOCK_LEN * 2;
const SELECT_ZEROS_PER_HINT: usize = SELECT_ONES_PER_HINT;

/// The index implementation of [`Rank9Sel`](crate::Rank9Sel) separated from the bit vector.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Rank9SelIndex {
    len: usize,
    block_rank_pairs: Vec<usize>,
    select1_hints: Option<Vec<usize>>,
    select0_hints: Option<Vec<usize>>,
}

impl Rank9SelIndex {
    /// Creates a new vector from input bit vector `bv`.
    pub fn new(bv: &BitVector) -> Self {
        Self::build_rank(bv)
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

    fn build_rank(bv: &BitVector) -> Self {
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
            len: bv.num_bits(),
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

    /// Gets the number of bits set.
    #[inline(always)]
    pub fn num_ones(&self) -> usize {
        self.block_rank_pairs[self.block_rank_pairs.len() - 2]
    }

    /// Gets the number of bits unset.
    #[inline(always)]
    pub fn num_zeros(&self) -> usize {
        self.len - self.num_ones()
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

    /// Returns the number of ones from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `bv.len() < pos`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector used in construction.
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Safety
    ///
    /// `bv` must be the one used in construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, rank9sel::inner::Rank9SelIndex};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::new(&bv);
    ///
    /// unsafe {
    ///     assert_eq!(idx.rank1(&bv, 1), Some(1));
    ///     assert_eq!(idx.rank1(&bv, 2), Some(1));
    ///     assert_eq!(idx.rank1(&bv, 3), Some(1));
    ///     assert_eq!(idx.rank1(&bv, 4), Some(2));
    ///     assert_eq!(idx.rank1(&bv, 5), None);
    /// }
    /// ```
    pub unsafe fn rank1(&self, bv: &BitVector, pos: usize) -> Option<usize> {
        if bv.num_bits() < pos {
            return None;
        }
        if pos == bv.num_bits() {
            return Some(self.num_ones());
        }
        let (sub_bpos, sub_left) = (pos / 64, pos % 64);
        let mut r = self.sub_block_rank(sub_bpos);
        if sub_left != 0 {
            r += broadword::popcount(bv.words()[sub_bpos] << (64 - sub_left));
        }
        Some(r)
    }

    /// Returns the number of zeros from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `bv.len() < pos`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector used in construction.
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Safety
    ///
    /// `bv` must be the one used in construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, rank9sel::inner::Rank9SelIndex};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::new(&bv);
    ///
    /// unsafe {
    ///     assert_eq!(idx.rank0(&bv, 1), Some(0));
    ///     assert_eq!(idx.rank0(&bv, 2), Some(1));
    ///     assert_eq!(idx.rank0(&bv, 3), Some(2));
    ///     assert_eq!(idx.rank0(&bv, 4), Some(2));
    ///     assert_eq!(idx.rank0(&bv, 5), None);
    /// }
    /// ```
    pub unsafe fn rank0(&self, bv: &BitVector, pos: usize) -> Option<usize> {
        Some(pos - self.rank1(bv, pos)?)
    }

    /// Searches the position of the `k`-th bit set, or
    /// [`None`] if `self.num_ones() <= k`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector used in construction.
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Safety
    ///
    /// `bv` must be the one used in construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, rank9sel::inner::Rank9SelIndex};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::new(&bv).select1_hints();
    ///
    /// unsafe {
    ///     assert_eq!(idx.select1(&bv, 0), Some(0));
    ///     assert_eq!(idx.select1(&bv, 1), Some(3));
    ///     assert_eq!(idx.select1(&bv, 2), None);
    /// }
    /// ```
    pub unsafe fn select1(&self, bv: &BitVector, k: usize) -> Option<usize> {
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
            + broadword::select_in_word(bv.words()[word_offset], k - cur_rank).unwrap();
        Some(sel)
    }

    /// Searches the position of the `k`-th bit unset, or
    /// [`None`] if `self.num_zeros() <= k`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector used in construction.
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Safety
    ///
    /// `bv` must be the one used in construction.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::bit_vectors::{BitVector, rank9sel::inner::Rank9SelIndex};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let idx = Rank9SelIndex::new(&bv).select0_hints();
    ///
    /// unsafe {
    ///     assert_eq!(idx.select0(&bv, 0), Some(1));
    ///     assert_eq!(idx.select0(&bv, 1), Some(2));
    ///     assert_eq!(idx.select0(&bv, 2), None);
    /// }
    /// ```
    pub unsafe fn select0(&self, bv: &BitVector, k: usize) -> Option<usize> {
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
            + broadword::select_in_word(!bv.words()[word_offset], k - cur_rank).unwrap();
        Some(sel)
    }
}

impl Serializable for Rank9SelIndex {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.len.serialize_into(&mut writer)?;
        mem += self.block_rank_pairs.serialize_into(&mut writer)?;
        mem += self.select1_hints.serialize_into(&mut writer)?;
        mem += self.select0_hints.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let len = usize::deserialize_from(&mut reader)?;
        let block_rank_pairs = Vec::<usize>::deserialize_from(&mut reader)?;
        let select1_hints = Option::<Vec<usize>>::deserialize_from(&mut reader)?;
        let select0_hints = Option::<Vec<usize>>::deserialize_from(&mut reader)?;
        Ok(Self {
            len,
            block_rank_pairs,
            select1_hints,
            select0_hints,
        })
    }

    fn size_in_bytes(&self) -> usize {
        self.len.size_in_bytes()
            + self.block_rank_pairs.size_in_bytes()
            + self.select1_hints.size_in_bytes()
            + self.select0_hints.size_in_bytes()
    }
}
