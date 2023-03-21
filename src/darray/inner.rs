//! Internal index structure of [`DArray`](crate::DArray).
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};

use anyhow::Result;

use crate::bit_vectors::BitVectorStat;
use crate::{broadword, BitVector, Serializable};

const BLOCK_LEN: usize = 1024;
const SUBBLOCK_LEN: usize = 32;
const MAX_IN_BLOCK_DISTANCE: usize = 1 << 16;

/// The index implementation of [`DArray`](crate::DArray) separated from the bit vector.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct DArrayIndex {
    block_inventory: Vec<isize>,
    subblock_inventory: Vec<u16>,
    overflow_positions: Vec<usize>,
    num_positions: usize,
    over_one: bool, // WANT_TODO(kampersanda): Solve with generics
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
    /// - `bv`: Bit vector used in construction.
    /// - `k`: Select query.
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
    /// use sucds::{BitVector, darray::inner::DArrayIndex};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let da = DArrayIndex::new(&bv, true);
    ///
    /// unsafe {
    ///     assert_eq!(da.select(&bv, 0), Some(0));
    ///     assert_eq!(da.select(&bv, 1), Some(3));
    ///     assert_eq!(da.select(&bv, 2), None);
    /// }
    /// ```
    ///
    /// You can perform selections over unset bits by specifying
    /// `Self::new(&bv, over_one=false)`.
    ///
    /// ```
    /// use sucds::{BitVector, darray::inner::DArrayIndex};
    ///
    /// let bv = BitVector::from_bits([true, false, false, true]);
    /// let da = DArrayIndex::new(&bv, false);
    ///
    /// unsafe {
    ///     assert_eq!(da.select(&bv, 0), Some(1));
    ///     assert_eq!(da.select(&bv, 1), Some(2));
    ///     assert_eq!(da.select(&bv, 2), None);
    /// }
    /// ```
    #[inline(always)]
    pub unsafe fn select(&self, bv: &BitVector, k: usize) -> Option<usize> {
        if self.num_ones() <= k {
            return None;
        }

        let block = k / BLOCK_LEN;
        let block_pos = self.block_inventory[block];

        if block_pos < 0 {
            let overflow_pos = (-block_pos - 1) as usize;
            return Some(self.overflow_positions[overflow_pos + (k % BLOCK_LEN)]);
        }

        let subblock = k / SUBBLOCK_LEN;
        let mut reminder = k % SUBBLOCK_LEN;
        let start_pos = block_pos as usize + self.subblock_inventory[subblock] as usize;

        let sel = if reminder == 0 {
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

            64 * word_idx + broadword::select_in_word(word, reminder).unwrap()
        };
        Some(sel)
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub const fn num_ones(&self) -> usize {
        self.num_positions
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
                if cur_pos >= bv.num_bits() {
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

impl Serializable for DArrayIndex {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.block_inventory.serialize_into(&mut writer)?;
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

    #[test]
    fn test_all_zeros_index() {
        let bv = BitVector::from_bit(false, 3);
        let da = DArrayIndex::new(&bv, true);
        unsafe {
            assert_eq!(da.select(&bv, 0), None);
        }
    }

    #[test]
    fn test_all_ones_index() {
        let bv = BitVector::from_bit(true, 3);
        let da = DArrayIndex::new(&bv, false);
        unsafe {
            assert_eq!(da.select(&bv, 0), None);
        }
    }
}
