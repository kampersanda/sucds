//! Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
#![cfg(target_pointer_width = "64")]

pub mod inner;

use std::io::{Read, Write};

use anyhow::Result;

use crate::rank9sel::inner::Rank9SelIndex;
use crate::{BitGetter, BitVector, Predecessor, Ranker, Searial, Selector, Successor};
use inner::DArrayIndex;

/// Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
///
/// This is a yet another Rust port of [succinct::darray](https://github.com/ot/succinct/blob/master/darray.hpp).
///
/// # Examples
///
/// ```
/// use sucds::{DArray, BitGetter, Ranker, Selector};
///
/// let da = DArray::from_bits([true, false, false, true]).enable_rank();
///
/// assert_eq!(da.len(), 4);
///
/// // Need BitGetter
/// assert_eq!(da.get_bit(1), Some(false));
///
/// // Need Ranker and enable_rank()
/// assert_eq!(da.rank1(1), Some(1));
/// assert_eq!(da.rank0(1), Some(0));
///
/// // Need Selector
/// assert_eq!(da.select1(0), Some(0));
/// assert_eq!(da.select1(1), Some(3));
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
    r9: Option<Rank9SelIndex>,
}

impl DArray {
    /// Creates a new instance from bit positions set in `bits`.
    ///
    /// # Arguments
    ///
    /// - `bits`: Bit stream.
    pub fn from_bits<I>(bits: I) -> Self
    where
        I: IntoIterator<Item = bool>,
    {
        let bv = BitVector::from_bits(bits);
        let da = DArrayIndex::new(&bv, true);
        Self { bv, da, r9: None }
    }

    /// Builds an index to enable rank, predecessor, and successor queries.
    #[must_use]
    pub fn enable_rank(mut self) -> Self {
        self.r9 = Some(Rank9SelIndex::new(&self.bv));
        self
    }

    /// Returns the reference of the internal bit vector.
    ///
    /// Use the iterators of [`BitVector`] to scan darray entries.
    pub const fn bit_vector(&self) -> &BitVector {
        &self.bv
    }

    /// Returns the reference of the internal select index.
    pub const fn da_index(&self) -> &DArrayIndex {
        &self.da
    }

    /// Returns the reference of the internal rank index.
    pub const fn r9_index(&self) -> Option<&Rank9SelIndex> {
        self.r9.as_ref()
    }

    /// Gets the number of bits.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.bv.len()
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.bv.is_empty()
    }

    /// Gets the number of bits set.
    #[inline(always)]
    pub fn num_ones(&self) -> usize {
        self.da.num_ones()
    }

    /// Gets the number of bits unset.
    #[inline(always)]
    pub fn num_zeros(&self) -> usize {
        self.len() - self.num_ones()
    }
}

impl BitGetter for DArray {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{DArray, BitGetter};
    ///
    /// let da = DArray::from_bits([true, false, false]);
    ///
    /// assert_eq!(da.get_bit(0), Some(true));
    /// assert_eq!(da.get_bit(1), Some(false));
    /// assert_eq!(da.get_bit(2), Some(false));
    /// assert_eq!(da.get_bit(3), None);
    /// ```
    fn get_bit(&self, pos: usize) -> Option<bool> {
        self.bv.get_bit(pos)
    }
}

impl Ranker for DArray {
    /// Returns the number of ones from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `self.len() < pos`.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Panics
    ///
    /// It panics if the index is not built by [`Self::enable_rank()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{DArray, Ranker};
    ///
    /// let da = DArray::from_bits([true, false, false, true]).enable_rank();
    ///
    /// assert_eq!(da.rank1(1), Some(1));
    /// assert_eq!(da.rank1(2), Some(1));
    /// assert_eq!(da.rank1(3), Some(1));
    /// assert_eq!(da.rank1(4), Some(2));
    /// assert_eq!(da.rank1(5), None);
    /// ```
    fn rank1(&self, pos: usize) -> Option<usize> {
        let r9 = self.r9.as_ref().expect("enable_rank() must be set up.");
        unsafe { r9.rank1(&self.bv, pos) }
    }

    /// Returns the number of zeros from the 0-th bit to the `pos-1`-th bit, or
    /// [`None`] if `self.len() < pos`.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Panics
    ///
    /// It panics if the index is not built by [`Self::enable_rank()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{DArray, Ranker};
    ///
    /// let da = DArray::from_bits([true, false, false, true]).enable_rank();
    ///
    /// assert_eq!(da.rank0(1), Some(0));
    /// assert_eq!(da.rank0(2), Some(1));
    /// assert_eq!(da.rank0(3), Some(2));
    /// assert_eq!(da.rank0(4), Some(2));
    /// assert_eq!(da.rank0(5), None);
    /// ```
    fn rank0(&self, pos: usize) -> Option<usize> {
        let r9 = self.r9.as_ref().expect("enable_rank() must be set up.");
        unsafe { r9.rank0(&self.bv, pos) }
    }
}

impl Selector for DArray {
    /// Returns the `k`-th smallest integer, or
    /// [`None`] if `self.len() <= k`.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{DArray, Selector};
    ///
    /// let da = DArray::from_bits([true, false, false, true]);
    ///
    /// assert_eq!(da.select1(0), Some(0));
    /// assert_eq!(da.select1(1), Some(3));
    /// assert_eq!(da.select1(2), None);
    /// ```
    fn select1(&self, k: usize) -> Option<usize> {
        unsafe { self.da.select(&self.bv, k) }
    }

    /// Panics always because this operation is not supported.
    fn select0(&self, _k: usize) -> Option<usize> {
        panic!("This operation is not supported.");
    }
}

impl Predecessor for DArray {
    /// Returns the largest bit position `pred` such that `pred <= pos` and the `pred`-th bit is set, or
    /// [`None`] if not found or `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Panics
    ///
    /// It panics if the index is not built by [`Self::enable_rank()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{DArray, Predecessor};
    ///
    /// let da = DArray::from_bits([false, true, false, true]).enable_rank();
    ///
    /// assert_eq!(da.predecessor1(3), Some(3));
    /// assert_eq!(da.predecessor1(2), Some(1));
    /// assert_eq!(da.predecessor1(1), Some(1));
    /// assert_eq!(da.predecessor1(0), None);
    /// ```
    fn predecessor1(&self, pos: usize) -> Option<usize> {
        self.r9.as_ref().expect("enable_rank() must be set up.");
        if self.len() <= pos {
            return None;
        }
        let k = self.rank1(pos + 1).unwrap();
        (k != 0).then(|| self.select1(k - 1).unwrap())
    }

    /// Panics always because this operation is not supported.
    fn predecessor0(&self, _pos: usize) -> Option<usize> {
        panic!("This operation is not supported.");
    }
}

impl Successor for DArray {
    /// Returns the smallest bit position `succ` such that `succ >= pos` and the `succ`-th bit is set, or
    /// [`None`] if not found or `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Bit position.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Panics
    ///
    /// It panics if the index is not built by [`Self::enable_rank()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{DArray, Successor};
    ///
    /// let da = DArray::from_bits([true, false, true, false]).enable_rank();
    ///
    /// assert_eq!(da.successor1(0), Some(0));
    /// assert_eq!(da.successor1(1), Some(2));
    /// assert_eq!(da.successor1(2), Some(2));
    /// assert_eq!(da.successor1(3), None);
    /// ```
    fn successor1(&self, pos: usize) -> Option<usize> {
        self.r9.as_ref().expect("enable_rank() must be set up.");
        if self.len() <= pos {
            return None;
        }
        let k = self.rank1(pos).unwrap();
        (k < self.num_ones()).then(|| self.select1(k).unwrap())
    }

    /// Panics always because this operation is not supported.
    fn successor0(&self, _pos: usize) -> Option<usize> {
        panic!("This operation is not supported.");
    }
}

impl Searial for DArray {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.bv.serialize_into(&mut writer)?;
        mem += self.da.serialize_into(&mut writer)?;
        mem += self.r9.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let bv = BitVector::deserialize_from(&mut reader)?;
        let da = DArrayIndex::deserialize_from(&mut reader)?;
        let r9 = Option::<Rank9SelIndex>::deserialize_from(&mut reader)?;
        Ok(Self { bv, da, r9 })
    }

    fn size_in_bytes(&self) -> usize {
        self.bv.size_in_bytes() + self.da.size_in_bytes() + self.r9.size_in_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_zeros() {
        let da = DArray::from_bits([false, false, false]);
        assert_eq!(da.select1(0), None);
    }

    #[test]
    #[should_panic]
    fn test_rank1() {
        let da = DArray::from_bits([false, true, false]);
        da.rank1(1);
    }

    #[test]
    #[should_panic]
    fn test_rank0() {
        let da = DArray::from_bits([false, true, false]);
        da.rank0(1);
    }

    #[test]
    #[should_panic]
    fn test_select1() {
        let da = DArray::from_bits([false, true, false]);
        da.select0(0);
    }

    #[test]
    #[should_panic]
    fn test_predecessor1() {
        let da = DArray::from_bits([false, true, false]);
        da.predecessor1(1);
    }

    #[test]
    #[should_panic]
    fn test_predecessor0() {
        let da = DArray::from_bits([false, true, false]);
        da.predecessor0(1);
    }

    #[test]
    #[should_panic]
    fn test_successor1() {
        let da = DArray::from_bits([false, true, false]);
        da.successor1(1);
    }

    #[test]
    #[should_panic]
    fn test_successor0() {
        let da = DArray::from_bits([false, true, false]);
        da.successor0(1);
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let da = DArray::from_bits([true, false, false, true]);
        let size = da.serialize_into(&mut bytes).unwrap();
        let other = DArray::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(da, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, da.size_in_bytes());
    }
}
