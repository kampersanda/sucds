#![cfg(target_pointer_width = "64")]

use crate::{broadword, BitVector};
use serde::{Deserialize, Serialize};

const BLOCK_LEN: usize = 8;
const SELECT_ONES_PER_HINT: usize = 64 * BLOCK_LEN * 2;
const SELECT_ZEROS_PER_HINT: usize = SELECT_ONES_PER_HINT;

/// Rank/select data structure over a bit vector through Vigna's rank9 and hinted selection techniques.
///
/// [`RsBitVector`] builds rank/select indexes on a bit vector.
/// For a bit vector of $`n`$ bits,
///  - the rank index takes $`0.25n`$ bits, and
///  - the select index takes $`0.03n`$ bits in addition to the space of the rank index.
///
/// This is a yet another Rust port of [succinct::rs_bit_vector](https://github.com/ot/succinct/blob/master/rs_bit_vector.hpp).
///
/// # Examples
///
/// ```
/// use sucds::RsBitVector;
///
/// let bv = RsBitVector::from_bits(&[true, false, false, true], true, true);
/// assert_eq!(bv.get_bit(1), false);
/// assert_eq!(bv.rank1(1), 1);
/// assert_eq!(bv.rank0(1), 0);
/// assert_eq!(bv.select1(1), 3);
/// assert_eq!(bv.select0(0), 1);
/// ```
///
/// # References
///
///  - S. Vigna, "Broadword implementation of rank/select queries," In WEA, 2008.
#[derive(Serialize, Deserialize, Default, Debug)]
pub struct RsBitVector {
    bv: BitVector,
    block_rank_pairs: Vec<usize>,
    select1_hints: Option<Vec<usize>>,
    select0_hints: Option<Vec<usize>>,
}

impl RsBitVector {
    /// Creates a new [`RsBitVector`] from input bit vector `bv`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Input bit vector.
    /// - `select1_hints`: Flag to build the index for select1.
    /// - `select0_hints`: Flag to build the index for select0.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{BitVector, RsBitVector};
    ///
    /// let bv = RsBitVector::new(BitVector::from_bits(&[true, false, false, true]), true, true);
    /// assert_eq!(bv.get_bit(1), false);
    /// assert_eq!(bv.rank1(1), 1);
    /// assert_eq!(bv.rank0(1), 0);
    /// assert_eq!(bv.select1(1), 3);
    /// assert_eq!(bv.select0(0), 1);
    /// ```
    pub fn new(bv: BitVector, select1_hints: bool, select0_hints: bool) -> Self {
        let mut this = Self::build_rank(bv);
        if select1_hints {
            this = this.build_select0();
        }
        if select0_hints {
            this = this.build_select1();
        }
        this
    }

    /// Creates a new [`RsBitVector`] from input bitset `bits`.
    ///
    /// # Arguments
    ///
    /// - `bits`: List of bits.
    /// - `select1_hints`: Flag to build the index for select1.
    /// - `select0_hints`: Flag to build the index for select0.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::RsBitVector;
    ///
    /// let bv = RsBitVector::from_bits(&[true, false, false, true], true, true);
    /// assert_eq!(bv.get_bit(1), false);
    /// assert_eq!(bv.rank1(1), 1);
    /// assert_eq!(bv.rank0(1), 0);
    /// assert_eq!(bv.select1(1), 3);
    /// assert_eq!(bv.select0(0), 1);
    /// ```
    pub fn from_bits<'a, I>(bits: I, select1_hints: bool, select0_hints: bool) -> Self
    where
        I: IntoIterator<Item = &'a bool>,
    {
        Self::new(BitVector::from_bits(bits), select1_hints, select0_hints)
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
    /// use sucds::RsBitVector;
    ///
    /// let bv = RsBitVector::from_bits(&[true, false, false, true], false, false);
    /// assert_eq!(bv.get_bit(0), true);
    /// assert_eq!(bv.get_bit(1), false);
    /// assert_eq!(bv.get_bit(2), false);
    /// assert_eq!(bv.get_bit(3), true);
    /// ```
    #[inline(always)]
    pub fn get_bit(&self, pos: usize) -> bool {
        self.bv.get_bit(pos)
    }

    /// Counts the number of ones from the zeroth bit to the `pos-1`-th bit.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::RsBitVector;
    ///
    /// let bv = RsBitVector::from_bits(&[true, false, false, true], false, false);
    /// assert_eq!(bv.rank1(1), 1);
    /// assert_eq!(bv.rank1(2), 1);
    /// assert_eq!(bv.rank1(3), 1);
    /// assert_eq!(bv.rank1(4), 2);
    /// ```
    #[inline(always)]
    pub fn rank1(&self, pos: usize) -> usize {
        debug_assert!(pos <= self.len());
        if pos == self.len() {
            return self.num_ones();
        }
        let (sub_bpos, sub_left) = (pos / 64, pos % 64);
        let mut r = self.sub_block_rank(sub_bpos);
        if sub_left != 0 {
            r += broadword::popcount(self.bv.get_word(sub_bpos) << (64 - sub_left));
        }
        r
    }

    /// Counts the number of zeros from the zeroth bit to the `pos-1`-th bit.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::RsBitVector;
    ///
    /// let bv = RsBitVector::from_bits(&[true, false, false, true], false, false);
    /// assert_eq!(bv.rank0(1), 0);
    /// assert_eq!(bv.rank0(2), 1);
    /// assert_eq!(bv.rank0(3), 2);
    /// assert_eq!(bv.rank0(4), 2);
    /// ```
    #[inline(always)]
    pub fn rank0(&self, pos: usize) -> usize {
        pos - self.rank1(pos)
    }

    /// Searches the position of the `k`-th bit set.
    ///
    /// # Arguments
    ///
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::RsBitVector;
    ///
    /// let bv = RsBitVector::from_bits(&[true, false, false, true], true, false);
    /// assert_eq!(bv.select1(0), 0);
    /// assert_eq!(bv.select1(1), 3);
    /// ```
    #[inline(always)]
    pub fn select1(&self, k: usize) -> usize {
        debug_assert!(k < self.num_ones());
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
        word_offset * 64 + broadword::select_in_word(self.bv.get_word(word_offset), k - cur_rank)
    }

    /// Searches the position of the `k`-th bit unset.
    ///
    /// # Arguments
    ///
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::RsBitVector;
    ///
    /// let bv = RsBitVector::from_bits(&[true, false, false, true], false, true);
    /// assert_eq!(bv.select0(0), 1);
    /// assert_eq!(bv.select0(1), 2);
    /// ```
    #[inline(always)]
    pub fn select0(&self, k: usize) -> usize {
        debug_assert!(k < self.num_zeros());
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
        word_offset * 64 + broadword::select_in_word(!self.bv.get_word(word_offset), k - cur_rank)
    }

    /// Gets the number of bits.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.bv.len()
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
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
            let word_pop = broadword::popcount(bv.get_word(i));

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
            assert_eq!(cur_rank, bv.rank1(i));
            if bits[i] {
                assert_eq!(i, bv.select1(cur_rank));
                cur_rank += 1;
            }
        }
        assert_eq!(cur_rank, bv.num_ones());
    }

    fn test_rank_select0(bits: &[bool], bv: &RsBitVector) {
        let mut cur_rank = 0;
        for i in 0..bits.len() {
            assert_eq!(cur_rank, bv.rank0(i));
            if !bits[i] {
                assert_eq!(i, bv.select0(cur_rank));
                cur_rank += 1;
            }
        }
        assert_eq!(cur_rank, bv.num_zeros());
    }

    #[test]
    fn test_random_bits() {
        for seed in 0..100 {
            let bits = gen_random_bits(10000, seed);
            let bv = RsBitVector::from_bits(&bits, true, true);
            test_rank_select1(&bits, &bv);
            test_rank_select0(&bits, &bv);
        }
    }

    #[test]
    fn test_serialize() {
        let bits = gen_random_bits(10000, 42);
        let bv = RsBitVector::from_bits(&bits, true, true);
        let bytes = bincode::serialize(&bv).unwrap();
        let other: RsBitVector = bincode::deserialize(&bytes).unwrap();
        assert_eq!(bv.len(), other.len());
        assert_eq!(bv.num_ones(), other.num_ones());
        assert_eq!(bv.num_zeros(), other.num_zeros());
        test_rank_select1(&bits, &other);
        test_rank_select0(&bits, &other);
    }
}
