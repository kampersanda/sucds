//! Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
#![cfg(target_pointer_width = "64")]

pub mod iter;

use std::io::{Read, Write};

use anyhow::Result;

use crate::darray::iter::Iter;
use crate::{broadword, BitVector, Searial};

const BLOCK_LEN: usize = 1024;
const SUBBLOCK_LEN: usize = 32;
const MAX_IN_BLOCK_DISTANCE: usize = 1 << 16;

/// Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
///
/// This is a yet another Rust port of [succinct::darray](https://github.com/ot/succinct/blob/master/darray.hpp).
///
/// # Examples
///
/// ```
/// use sucds::DArray;
///
/// let da = DArray::from_bits([true, false, false, true]);
///
/// assert_eq!(da.select(0), 0);
/// assert_eq!(da.select(1), 3);
/// ```
///
/// # References
///
///  - D. Okanohara, and K. Sadakane, "Practical Entropy-Compressed Rank/Select Dictionary,"
///    In ALENEX, 2007.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct DArray {
    bv: BitVector,
    da: DArrayIndex,
}

impl DArray {
    /// Creates a new [`DArray`] from input bitset `bits`.
    ///
    /// # Arguments
    ///
    /// - `bits`: List of bits.
    pub fn from_bits<I>(bits: I) -> Self
    where
        I: IntoIterator<Item = bool>,
    {
        let bv = BitVector::from_bits(bits);
        Self {
            da: DArrayIndex::build(&bv, true),
            bv,
        }
    }

    /// Searches the `k`-th iteger.
    ///
    /// # Arguments
    ///
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::DArray;
    ///
    /// let da = DArray::from_bits([true, false, false, true]);
    /// assert_eq!(da.select(0), 0);
    /// assert_eq!(da.select(1), 3);
    /// ```
    #[inline(always)]
    pub fn select(&self, k: usize) -> usize {
        self.da.select(&self.bv, k)
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::DArray;
    ///
    /// let da = DArray::from_bits([true, false, false, true]);
    /// let mut it = da.iter();
    ///
    /// assert_eq!(it.next(), Some(0));
    /// assert_eq!(it.next(), Some(3));
    /// assert_eq!(it.next(), None);
    /// ```
    pub const fn iter(&self) -> Iter {
        Iter::new(self)
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.da.len()
    }

    /// Checks if the set is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.da.is_empty()
    }
}

impl Searial for DArray {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mem = self.bv.serialize_into(&mut writer)? + self.da.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let bv = BitVector::deserialize_from(&mut reader)?;
        let da = DArrayIndex::deserialize_from(&mut reader)?;
        Ok(Self { bv, da })
    }

    fn size_in_bytes(&self) -> usize {
        self.bv.size_in_bytes() + self.da.size_in_bytes()
    }
}

/// The index implementation of [`DArray`] separated from the bit vector.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct DArrayIndex {
    block_inventory: Vec<isize>,
    subblock_inventory: Vec<u16>,
    overflow_positions: Vec<usize>,
    num_positions: usize,
    over_one: bool, // TODO: Solve with generics
}

impl DArrayIndex {
    /// Creates a new [`DArrayIndex`] from input bit vector `bv`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Input bit vector.
    /// - `over_one`: Flag to build the index for ones.
    pub fn new(bv: &BitVector, over_one: bool) -> Self {
        Self::build(bv, over_one)
    }

    /// Searches the `k`-th iteger.
    ///
    /// # Arguments
    ///
    /// - `bv`: Bit vector (used to build).
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{BitVector, darray::DArrayIndex};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let da = DArrayIndex::new(&bv, true);
    /// assert_eq!(da.select(&bv, 0), 0);
    /// assert_eq!(da.select(&bv, 1), 3);
    /// ```
    #[inline(always)]
    pub fn select(&self, bv: &BitVector, k: usize) -> usize {
        debug_assert!(k < self.num_positions);

        let block = k / BLOCK_LEN;
        let block_pos = self.block_inventory[block];

        if block_pos < 0 {
            let overflow_pos = (-block_pos - 1) as usize;
            return self.overflow_positions[overflow_pos + (k % BLOCK_LEN)];
        }

        let subblock = k / SUBBLOCK_LEN;
        let mut reminder = k % SUBBLOCK_LEN;
        let start_pos = block_pos as usize + self.subblock_inventory[subblock] as usize;

        if reminder == 0 {
            start_pos
        } else {
            let w = {
                if self.over_one {
                    Self::get_word_over_one
                } else {
                    Self::get_word_over_zero
                }
            };

            let mut word_idx = start_pos / 64;
            let word_shift = start_pos % 64;
            let mut word = w(bv, word_idx) & (std::usize::MAX << word_shift);

            loop {
                let popcnt = broadword::popcount(word);
                if reminder < popcnt {
                    break;
                }
                reminder -= popcnt;
                word_idx += 1;
                word = w(bv, word_idx);
            }

            64 * word_idx + broadword::select_in_word(word, reminder)
        }
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.num_positions
    }

    /// Checks if the set is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn build(bv: &BitVector, over_one: bool) -> Self {
        let mut cur_block_positions = vec![];
        let mut block_inventory = vec![];
        let mut subblock_inventory = vec![];
        let mut overflow_positions = vec![];
        let mut num_positions = 0;

        let w = {
            if over_one {
                Self::get_word_over_one
            } else {
                Self::get_word_over_zero
            }
        };

        for word_idx in 0..bv.num_words() {
            let mut cur_pos = word_idx * 64;
            let mut cur_word = w(bv, word_idx);

            while let Some(l) = broadword::lsb(cur_word) {
                cur_pos += l;
                cur_word >>= l;
                if cur_pos >= bv.len() {
                    break;
                }

                cur_block_positions.push(cur_pos);
                if cur_block_positions.len() == BLOCK_LEN {
                    Self::flush_cur_block(
                        &mut cur_block_positions,
                        &mut block_inventory,
                        &mut subblock_inventory,
                        &mut overflow_positions,
                    );
                }

                cur_word >>= 1;
                cur_pos += 1;
                num_positions += 1;
            }
        }

        if !cur_block_positions.is_empty() {
            Self::flush_cur_block(
                &mut cur_block_positions,
                &mut block_inventory,
                &mut subblock_inventory,
                &mut overflow_positions,
            );
        }

        block_inventory.shrink_to_fit();
        subblock_inventory.shrink_to_fit();
        overflow_positions.shrink_to_fit();

        Self {
            block_inventory,
            subblock_inventory,
            overflow_positions,
            num_positions,
            over_one,
        }
    }

    fn flush_cur_block(
        cur_block_positions: &mut Vec<usize>,
        block_inventory: &mut Vec<isize>,
        subblock_inventory: &mut Vec<u16>,
        overflow_positions: &mut Vec<usize>,
    ) {
        let &first = cur_block_positions.first().unwrap();
        let &last = cur_block_positions.last().unwrap();
        if last - first < MAX_IN_BLOCK_DISTANCE {
            block_inventory.push(first as isize);
            for i in (0..cur_block_positions.len()).step_by(SUBBLOCK_LEN) {
                subblock_inventory.push((cur_block_positions[i] - first) as u16);
            }
        } else {
            block_inventory.push(-((overflow_positions.len() + 1) as isize));
            for &x in cur_block_positions.iter() {
                overflow_positions.push(x);
            }
            for _ in (0..cur_block_positions.len()).step_by(SUBBLOCK_LEN) {
                subblock_inventory.push(std::u16::MAX);
            }
        }
        cur_block_positions.clear();
    }

    fn get_word_over_one(bv: &BitVector, word_idx: usize) -> usize {
        bv.words()[word_idx]
    }

    fn get_word_over_zero(bv: &BitVector, word_idx: usize) -> usize {
        !bv.words()[word_idx]
    }
}

impl Searial for DArrayIndex {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = self.block_inventory.serialize_into(&mut writer)?;
        mem += self.subblock_inventory.serialize_into(&mut writer)?;
        mem += self.overflow_positions.serialize_into(&mut writer)?;
        mem += self.num_positions.serialize_into(&mut writer)?;
        mem += self.over_one.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let block_inventory = Vec::<isize>::deserialize_from(&mut reader)?;
        let subblock_inventory = Vec::<u16>::deserialize_from(&mut reader)?;
        let overflow_positions = Vec::<usize>::deserialize_from(&mut reader)?;
        let num_positions = usize::deserialize_from(&mut reader)?;
        let over_one = bool::deserialize_from(&mut reader)?;
        Ok(Self {
            block_inventory,
            subblock_inventory,
            overflow_positions,
            num_positions,
            over_one,
        })
    }

    fn size_in_bytes(&self) -> usize {
        self.block_inventory.size_in_bytes()
            + self.subblock_inventory.size_in_bytes()
            + self.overflow_positions.size_in_bytes()
            + usize::size_of().unwrap()
            + bool::size_of().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn gen_random_bits(len: usize, p: f64, seed: u64) -> Vec<bool> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen_bool(p)).collect()
    }

    fn test_select(bv: &BitVector, da: &DArrayIndex) {
        let mut cur_rank = 0;
        for i in 0..bv.len() {
            if bv.get_bit(i) {
                assert_eq!(i, da.select(bv, cur_rank));
                cur_rank += 1;
            }
        }
        assert_eq!(cur_rank, da.len());
    }

    fn test_select0(bv: &BitVector, da: &DArrayIndex) {
        let mut cur_rank = 0;
        for i in 0..bv.len() {
            if !bv.get_bit(i) {
                assert_eq!(i, da.select(bv, cur_rank));
                cur_rank += 1;
            }
        }
    }

    #[test]
    fn test_tiny_bits() {
        let bv = BitVector::from_bits([true, false, false, true, false, true, true]);
        let da = DArrayIndex::new(&bv, true);
        assert_eq!(da.select(&bv, 0), 0);
        assert_eq!(da.select(&bv, 1), 3);
        assert_eq!(da.select(&bv, 2), 5);
        assert_eq!(da.select(&bv, 3), 6);
        let da = DArrayIndex::new(&bv, false);
        assert_eq!(da.select(&bv, 0), 1);
        assert_eq!(da.select(&bv, 1), 2);
        assert_eq!(da.select(&bv, 2), 4);
    }

    #[test]
    fn test_random_bits_dense() {
        for seed in 0..100 {
            let bv = BitVector::from_bits(gen_random_bits(10000, 0.5, seed));
            let da = DArrayIndex::new(&bv, true);
            test_select(&bv, &da);
            let da = DArrayIndex::new(&bv, false);
            test_select0(&bv, &da);
        }
    }

    #[test]
    fn test_random_bits_sparse() {
        for seed in 0..100 {
            let bv = BitVector::from_bits(gen_random_bits(10000, 0.01, seed));
            let da = DArrayIndex::new(&bv, true);
            test_select(&bv, &da);
            let da = DArrayIndex::new(&bv, false);
            test_select0(&bv, &da);
        }
    }

    #[test]
    fn test_serialize_dense() {
        let mut bytes = vec![];
        let da = DArray::from_bits(gen_random_bits(10000, 0.5, 42));
        let size = da.serialize_into(&mut bytes).unwrap();
        let other = DArray::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(da, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, da.size_in_bytes());
    }

    #[test]
    fn test_serialize_sparse() {
        let mut bytes = vec![];
        let da = DArray::from_bits(gen_random_bits(10000, 0.01, 42));
        let size = da.serialize_into(&mut bytes).unwrap();
        let other = DArray::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(da, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, da.size_in_bytes());
    }
}
