//! Rank/Select data structure over very sparse bit vectors.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};

use anyhow::Result;

use crate::broadword;
use crate::{BitGetter, BitVector, EliasFano, EliasFanoBuilder, Ranker, Selector, Serializable};

/// Rank/Select data structure over very sparse bit vectors.
///
/// This is a specialized version of [EliasFano](crate::EliasFano) for bit vectors.
///
/// # References
///
///  - D. Okanohara, and K. Sadakane, "Practical Entropy-Compressed Rank/Select Dictionary,"
///    In ALENEX, 2007.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct SArray {
    ef: Option<EliasFano>, // None if num_bits == 0.
    num_bits: usize,
    num_ones: usize,
    has_rank: bool,
}

impl SArray {
    /// Creates a new instance from input bit stream `bits`.
    ///
    /// # Arguments
    ///
    /// - `bits`: Bit stream.
    pub fn from_bits<I>(bits: I) -> Self
    where
        I: IntoIterator<Item = bool>,
    {
        let bv = BitVector::from_bits(bits);
        let num_bits = bv.len();
        let num_ones =
            (0..bv.num_words()).fold(0, |acc, i| acc + broadword::popcount(bv.words()[i]));
        let ef = if num_ones != 0 {
            let mut b = EliasFanoBuilder::new(num_bits, num_ones).unwrap();
            for i in bv.unary_iter(0) {
                b.push(i).unwrap();
            }
            Some(b.build())
        } else {
            None
        };
        Self {
            ef,
            num_bits,
            num_ones,
            has_rank: false,
        }
    }

    /// Builds an index to enable rank, predecessor, and successor queries.
    #[must_use]
    pub fn enable_rank(mut self) -> Self {
        if let Some(ef) = self.ef {
            self.ef = Some(ef.enable_rank());
        }
        self.has_rank = true;
        self
    }

    /// Checks if [`Self::enable_rank()`] is set.
    pub fn has_rank(&self) -> bool {
        self.has_rank
    }
}

impl BitGetter for SArray {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// - $`O(\log n)`$
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{SArray, BitGetter};
    ///
    /// let sa = SArray::from_bits([true, false, false]);
    ///
    /// assert_eq!(sa.get_bit(0), Some(true));
    /// assert_eq!(sa.get_bit(1), Some(false));
    /// assert_eq!(sa.get_bit(2), Some(false));
    /// assert_eq!(sa.get_bit(3), None);
    /// ```
    fn get_bit(&self, pos: usize) -> Option<bool> {
        if self.num_bits <= pos {
            return None;
        }
        if let Some(ef) = self.ef.as_ref() {
            Some(ef.binsearch(pos).is_some())
        } else {
            Some(false)
        }
    }
}

impl Ranker for SArray {
    /// Returns the number of ones from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `self.len() < pos`.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \frac{u}{n})`$
    ///
    /// # Panics
    ///
    /// It panics if the index is not built by [`Self::enable_rank()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{SArray, Ranker};
    ///
    /// let sa = SArray::from_bits([true, false, false, true]).enable_rank();
    ///
    /// assert_eq!(sa.rank1(1), Some(1));
    /// assert_eq!(sa.rank1(2), Some(1));
    /// assert_eq!(sa.rank1(3), Some(1));
    /// assert_eq!(sa.rank1(4), Some(2));
    /// assert_eq!(sa.rank1(5), None);
    /// ```
    fn rank1(&self, pos: usize) -> Option<usize> {
        if !self.has_rank() {
            panic!("enable_rank() must be set up.")
        }
        if let Some(ef) = self.ef.as_ref() {
            ef.rank1(pos)
        } else {
            Some(0)
        }
    }

    /// Returns the number of zeros from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `self.len() < pos`.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \frac{u}{n})`$
    ///
    /// # Panics
    ///
    /// It panics if the index is not built by [`Self::enable_rank()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{SArray, Ranker};
    ///
    /// let sa = SArray::from_bits([true, false, false, true]).enable_rank();
    ///
    /// assert_eq!(sa.rank0(1), Some(0));
    /// assert_eq!(sa.rank0(2), Some(1));
    /// assert_eq!(sa.rank0(3), Some(2));
    /// assert_eq!(sa.rank0(4), Some(2));
    /// assert_eq!(sa.rank0(5), None);
    /// ```
    fn rank0(&self, pos: usize) -> Option<usize> {
        Some(pos - self.rank1(pos)?)
    }
}

impl Selector for SArray {
    /// Searches the position of the `k`-th bit set, or
    /// [`None`] if `self.num_ones() <= k`.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{SArray, Selector};
    ///
    /// let sa = SArray::from_bits([true, false, false, true]);
    ///
    /// assert_eq!(sa.select1(0), Some(0));
    /// assert_eq!(sa.select1(1), Some(3));
    /// assert_eq!(sa.select1(2), None);
    /// ```
    fn select1(&self, k: usize) -> Option<usize> {
        if let Some(ef) = self.ef.as_ref() {
            ef.select1(k)
        } else {
            None
        }
    }

    /// Panics always because this operation is not supported.
    fn select0(&self, _k: usize) -> Option<usize> {
        panic!("This operation is not supported.");
    }
}

impl Serializable for SArray {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.ef.serialize_into(&mut writer)?;
        mem += self.num_bits.serialize_into(&mut writer)?;
        mem += self.num_ones.serialize_into(&mut writer)?;
        mem += self.has_rank.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let ef = Option::<EliasFano>::deserialize_from(&mut reader)?;
        let num_bits = usize::deserialize_from(&mut reader)?;
        let num_ones = usize::deserialize_from(&mut reader)?;
        let has_rank = bool::deserialize_from(&mut reader)?;
        Ok(Self {
            ef,
            num_bits,
            num_ones,
            has_rank,
        })
    }

    fn size_in_bytes(&self) -> usize {
        self.ef.size_in_bytes()
            + self.num_bits.size_in_bytes()
            + self.num_ones.size_in_bytes()
            + self.has_rank.size_in_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_zeros() {
        let sa = SArray::from_bits([false, false, false]);
        assert_eq!(sa.select1(0), None);
    }

    #[test]
    #[should_panic]
    fn test_rank1_panic() {
        let sa = SArray::from_bits([false, true, false]);
        sa.rank1(1);
    }

    #[test]
    #[should_panic]
    fn test_rank0_panic() {
        let sa = SArray::from_bits([false, true, false]);
        sa.rank0(1);
    }

    #[test]
    #[should_panic]
    fn test_select0_panic() {
        let sa = SArray::from_bits([false, true, false]);
        sa.select0(0);
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let sa = SArray::from_bits([true, false, false, true]);
        let size = sa.serialize_into(&mut bytes).unwrap();
        let other = SArray::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(sa, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, sa.size_in_bytes());
    }
}
