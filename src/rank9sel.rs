//! Rank/select data structure over bit vectors with Vigna's rank9 and hinted selection techniques.
#![cfg(target_pointer_width = "64")]

pub mod inner;

use std::io::{Read, Write};

use anyhow::Result;

use crate::{BitGetter, BitVector, Predecessor, Ranker, Searial, Selector, Successor};
use inner::Rank9SelIndex;

/// Rank/select data structure over bit vectors with Vigna's rank9 and hinted selection techniques.
///
/// This builds rank/select indices on [`BitVector`] taking
///
/// - 25% overhead of space for the rank index, and
/// - 3% overhead of space for the select index (together with the rank's overhead).
///
/// This is a yet another Rust port of [succinct::rs_bit_vector](https://github.com/ot/succinct/blob/master/rs_bit_vector.hpp).
///
/// # Examples
///
/// ```
/// use sucds::{Rank9Sel, BitGetter, Ranker, Selector};
///
/// let bv = Rank9Sel::from_bits([true, false, false, true])
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
pub struct Rank9Sel {
    bv: BitVector,
    rs: Rank9SelIndex,
}

impl Rank9Sel {
    /// Creates a new vector from input bit vector `bv`.
    pub fn new(bv: BitVector) -> Self {
        let rs = Rank9SelIndex::new(&bv);
        Self { bv, rs }
    }

    /// Builds an index for faster `select1`, `predecessor1`, and `successor1`.
    #[must_use]
    pub fn select1_hints(mut self) -> Self {
        self.rs = self.rs.select1_hints();
        self
    }

    /// Builds an index for faster `select0`, `predecessor0`, and `successor0`.
    #[must_use]
    pub fn select0_hints(mut self) -> Self {
        self.rs = self.rs.select0_hints();
        self
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

    /// Returns the reference of the internal bit vector.
    pub const fn bit_vector(&self) -> &BitVector {
        &self.bv
    }

    /// Returns the reference of the internal rank/select index.
    pub const fn rs_index(&self) -> &Rank9SelIndex {
        &self.rs
    }

    /// Returns the number of bits.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.bv.len()
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the number of bits set.
    #[inline(always)]
    pub fn num_ones(&self) -> usize {
        self.rs.num_ones()
    }

    /// Returns the number of bits unset.
    #[inline(always)]
    pub fn num_zeros(&self) -> usize {
        self.rs.num_zeros()
    }
}

impl BitGetter for Rank9Sel {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Rank9Sel, BitGetter};
    ///
    /// let bv = Rank9Sel::from_bits([true, false, false]);
    ///
    /// assert_eq!(bv.get_bit(0), Some(true));
    /// assert_eq!(bv.get_bit(1), Some(false));
    /// assert_eq!(bv.get_bit(2), Some(false));
    /// assert_eq!(bv.get_bit(3), None);
    /// ```
    fn get_bit(&self, pos: usize) -> Option<bool> {
        self.bv.get_bit(pos)
    }
}

impl Ranker for Rank9Sel {
    /// Returns the number of ones from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `self.len() < pos`.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Ranker, Rank9Sel};
    ///
    /// let bv = Rank9Sel::from_bits([true, false, false, true]);
    ///
    /// assert_eq!(bv.rank1(1), Some(1));
    /// assert_eq!(bv.rank1(2), Some(1));
    /// assert_eq!(bv.rank1(3), Some(1));
    /// assert_eq!(bv.rank1(4), Some(2));
    /// assert_eq!(bv.rank1(5), None);
    /// ```
    fn rank1(&self, pos: usize) -> Option<usize> {
        unsafe { self.rs.rank1(&self.bv, pos) }
    }

    /// Returns the number of zeros from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `self.len() < pos`.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Ranker, Rank9Sel};
    ///
    /// let bv = Rank9Sel::from_bits([true, false, false, true]);
    ///
    /// assert_eq!(bv.rank0(1), Some(0));
    /// assert_eq!(bv.rank0(2), Some(1));
    /// assert_eq!(bv.rank0(3), Some(2));
    /// assert_eq!(bv.rank0(4), Some(2));
    /// assert_eq!(bv.rank0(5), None);
    /// ```
    fn rank0(&self, pos: usize) -> Option<usize> {
        unsafe { self.rs.rank0(&self.bv, pos) }
    }
}

impl Selector for Rank9Sel {
    /// Searches the position of the `k`-th bit set, or
    /// [`None`] if `self.num_ones() <= k`.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Rank9Sel, Selector};
    ///
    /// let bv = Rank9Sel::from_bits([true, false, false, true]).select1_hints();
    ///
    /// assert_eq!(bv.select1(0), Some(0));
    /// assert_eq!(bv.select1(1), Some(3));
    /// assert_eq!(bv.select1(2), None);
    /// ```
    fn select1(&self, k: usize) -> Option<usize> {
        unsafe { self.rs.select1(&self.bv, k) }
    }

    /// Searches the position of the `k`-th bit unset, or
    /// [`None`] if `self.num_zeros() <= k`.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Rank9Sel, Selector};
    ///
    /// let bv = Rank9Sel::from_bits([true, false, false, true]).select0_hints();
    ///
    /// assert_eq!(bv.select0(0), Some(1));
    /// assert_eq!(bv.select0(1), Some(2));
    /// assert_eq!(bv.select0(2), None);
    /// ```
    fn select0(&self, k: usize) -> Option<usize> {
        unsafe { self.rs.select0(&self.bv, k) }
    }
}

impl Predecessor for Rank9Sel {
    /// Returns the largest bit position `pred` such that `pred <= pos` and the `pred`-th bit is set, or
    /// [`None`] if not found or `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Rank9Sel, Predecessor};
    ///
    /// let bv = Rank9Sel::from_bits([false, true, false, true]).select1_hints();
    ///
    /// assert_eq!(bv.predecessor1(3), Some(3));
    /// assert_eq!(bv.predecessor1(2), Some(1));
    /// assert_eq!(bv.predecessor1(1), Some(1));
    /// assert_eq!(bv.predecessor1(0), None);
    /// ```
    fn predecessor1(&self, pos: usize) -> Option<usize> {
        if self.len() <= pos {
            return None;
        }
        let k = self.rank1(pos + 1).unwrap();
        (k != 0).then(|| self.select1(k - 1).unwrap())
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
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Rank9Sel, Predecessor};
    ///
    /// let bv = Rank9Sel::from_bits([true, false, true, false]).select0_hints();
    ///
    /// assert_eq!(bv.predecessor0(3), Some(3));
    /// assert_eq!(bv.predecessor0(2), Some(1));
    /// assert_eq!(bv.predecessor0(1), Some(1));
    /// assert_eq!(bv.predecessor0(0), None);
    /// ```
    fn predecessor0(&self, pos: usize) -> Option<usize> {
        if self.len() <= pos {
            return None;
        }
        let k = self.rank0(pos + 1).unwrap();
        (k != 0).then(|| self.select0(k - 1).unwrap())
    }
}

impl Successor for Rank9Sel {
    /// Returns the smallest bit position `succ` such that `succ >= pos` and the `succ`-th bit is set, or
    /// [`None`] if not found or `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Rank9Sel, Successor};
    ///
    /// let bv = Rank9Sel::from_bits([true, false, true, false]).select1_hints();
    ///
    /// assert_eq!(bv.successor1(0), Some(0));
    /// assert_eq!(bv.successor1(1), Some(2));
    /// assert_eq!(bv.successor1(2), Some(2));
    /// assert_eq!(bv.successor1(3), None);
    /// ```
    fn successor1(&self, pos: usize) -> Option<usize> {
        if self.len() <= pos {
            return None;
        }
        let k = self.rank1(pos).unwrap();
        (k < self.num_ones()).then(|| self.select1(k).unwrap())
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
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{Rank9Sel, Successor};
    ///
    /// let bv = Rank9Sel::from_bits([false, true, false, true]).select0_hints();
    ///
    /// assert_eq!(bv.successor0(0), Some(0));
    /// assert_eq!(bv.successor0(1), Some(2));
    /// assert_eq!(bv.successor0(2), Some(2));
    /// assert_eq!(bv.successor0(3), None);
    /// ```
    fn successor0(&self, pos: usize) -> Option<usize> {
        if self.len() <= pos {
            return None;
        }
        let k = self.rank0(pos).unwrap();
        (k < self.num_zeros()).then(|| self.select0(k).unwrap())
    }
}

impl Searial for Rank9Sel {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.bv.serialize_into(&mut writer)?;
        mem += self.rs.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let bv = BitVector::deserialize_from(&mut reader)?;
        let rs = Rank9SelIndex::deserialize_from(&mut reader)?;
        Ok(Self { bv, rs })
    }

    fn size_in_bytes(&self) -> usize {
        self.bv.size_in_bytes() + self.rs.size_in_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rank1_all_zeros() {
        let bv = Rank9Sel::from_bits([false, false, false]);
        assert_eq!(bv.rank1(0), Some(0));
        assert_eq!(bv.rank1(1), Some(0));
        assert_eq!(bv.rank1(2), Some(0));
        assert_eq!(bv.rank1(3), Some(0));
        assert_eq!(bv.rank1(4), None);
    }

    #[test]
    fn test_select1_all_zeros() {
        let bv = Rank9Sel::from_bits([false, false, false]).select1_hints();
        assert_eq!(bv.select1(0), None);
    }

    #[test]
    fn test_rank0_all_ones() {
        let bv = Rank9Sel::from_bits([true, true, true]);
        assert_eq!(bv.rank0(0), Some(0));
        assert_eq!(bv.rank0(1), Some(0));
        assert_eq!(bv.rank0(2), Some(0));
        assert_eq!(bv.rank0(3), Some(0));
        assert_eq!(bv.rank0(4), None);
    }

    #[test]
    fn test_select0_all_ones() {
        let bv = Rank9Sel::from_bits([true, true, true]).select0_hints();
        assert_eq!(bv.select0(0), None);
    }

    #[test]
    fn test_select0_no_hint() {
        let bv = Rank9Sel::from_bits([true, false, false, true]);
        assert_eq!(bv.select0(0), Some(1));
        assert_eq!(bv.select0(1), Some(2));
        assert_eq!(bv.select0(2), None);
    }

    #[test]
    fn test_select1_no_hint() {
        let bv = Rank9Sel::from_bits([true, false, false, true]);
        assert_eq!(bv.select1(0), Some(0));
        assert_eq!(bv.select1(1), Some(3));
        assert_eq!(bv.select1(2), None);
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let bv = Rank9Sel::from_bits([false, true, true, false, true])
            .select1_hints()
            .select0_hints();
        let size = bv.serialize_into(&mut bytes).unwrap();
        let other = Rank9Sel::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(bv, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, bv.size_in_bytes());
    }
}
