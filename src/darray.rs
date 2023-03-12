//! Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
#![cfg(target_pointer_width = "64")]

pub mod inner;

use std::io::{Read, Write};

use anyhow::Result;

use crate::rank9sel::inner::Rank9SelIndex;
use crate::{
    BitGetter, BitVector, Predecessor, Ranker, RsbvBuilder, Selector, Serializable, Successor,
};
use inner::DArrayIndex;

/// Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
///
/// This is a yet another Rust port of [succinct::darray](https://github.com/ot/succinct/blob/master/darray.hpp).
///
/// # Notes
///
/// In the default configuration, this data structure supports only [`Self::select1()`].
/// If other operations are needed, [`Self::enable_rank()`] and [`Self::enable_select0()`] must be set up.
///
/// # Examples
///
/// ```
/// use sucds::{DArray, BitGetter, Ranker, Selector};
///
/// let da = DArray::from_bits([true, false, false, true])
///     .enable_rank()
///     .enable_select0();
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
/// assert_eq!(da.select1(1), Some(3));
/// assert_eq!(da.select0(0), Some(1)); // Need enable_select0()
/// ```
///
/// # References
///
///  - D. Okanohara, and K. Sadakane, "Practical Entropy-Compressed Rank/Select Dictionary,"
///    In ALENEX, 2007.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct DArray {
    bv: BitVector,
    s1: DArrayIndex,
    s0: Option<DArrayIndex>,
    r9: Option<Rank9SelIndex>,
}

impl DArray {
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
        let s1 = DArrayIndex::new(&bv, true);
        Self {
            bv,
            s1,
            s0: None,
            r9: None,
        }
    }

    /// Builds an index to enable rank, predecessor, and successor queries.
    #[must_use]
    pub fn enable_rank(mut self) -> Self {
        self.r9 = Some(Rank9SelIndex::new(&self.bv));
        self
    }

    /// Builds an index to enable select0, predecessor0, and successor0 queries.
    #[must_use]
    pub fn enable_select0(mut self) -> Self {
        self.s0 = Some(DArrayIndex::new(&self.bv, false));
        self
    }

    /// Checks if [`Self::enable_rank()`] is set.
    #[inline(always)]
    pub const fn has_rank(&self) -> bool {
        self.r9.is_some()
    }

    /// Checks if [`Self::enable_select0()`] is set.
    #[inline(always)]
    pub const fn has_select0(&self) -> bool {
        self.s0.is_some()
    }

    /// Returns the reference of the internal bit vector.
    ///
    /// Use the iterators of [`BitVector`] to scan darray entries.
    pub const fn bit_vector(&self) -> &BitVector {
        &self.bv
    }

    /// Returns the reference of the internal select1 index.
    pub const fn s1_index(&self) -> &DArrayIndex {
        &self.s1
    }

    /// Returns the reference of the internal select0 index.
    pub const fn s0_index(&self) -> Option<&DArrayIndex> {
        self.s0.as_ref()
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
    pub const fn num_ones(&self) -> usize {
        self.s1.num_ones()
    }

    /// Gets the number of bits unset.
    #[inline(always)]
    pub const fn num_zeros(&self) -> usize {
        self.len() - self.num_ones()
    }
}

impl RsbvBuilder for DArray {
    /// Creates a new vector from input bit stream `bits`.
    ///
    /// # Arguments
    ///
    /// - `bits`: Bit stream.
    /// - `with_rank`: Flag to enable [`Self::enable_rank()`].
    /// - `with_select1`: Dummy.
    /// - `with_select0`: Flag to enable [`Self::enable_select0()`].
    ///
    /// # Errors
    ///
    /// Never.
    fn build_from_bits<I>(
        bits: I,
        with_rank: bool,
        _with_select1: bool,
        with_select0: bool,
    ) -> Result<Self>
    where
        I: IntoIterator<Item = bool>,
        Self: Sized,
    {
        let mut rsbv = Self::from_bits(bits);
        if with_rank {
            rsbv = rsbv.enable_rank();
        }
        if with_select0 {
            rsbv = rsbv.enable_select0();
        }
        Ok(rsbv)
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
    /// use sucds::{DArray, Selector};
    ///
    /// let da = DArray::from_bits([true, false, false, true]);
    ///
    /// assert_eq!(da.select1(0), Some(0));
    /// assert_eq!(da.select1(1), Some(3));
    /// assert_eq!(da.select1(2), None);
    /// ```
    fn select1(&self, k: usize) -> Option<usize> {
        unsafe { self.s1.select(&self.bv, k) }
    }

    /// Searches the position of the `k`-th bit unset, or
    /// [`None`] if `self.num_zeros() <= k`.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Panics
    ///
    /// It panics if the index is not built by [`Self::enable_select0()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{DArray, Selector};
    ///
    /// let da = DArray::from_bits([true, false, false, true]).enable_select0();
    ///
    /// assert_eq!(da.select0(0), Some(1));
    /// assert_eq!(da.select0(1), Some(2));
    /// assert_eq!(da.select0(2), None);
    /// ```
    fn select0(&self, k: usize) -> Option<usize> {
        let s0 = self.s0.as_ref().expect("enable_select0() must be set up.");
        unsafe { s0.select(&self.bv, k) }
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

    /// Returns the largest bit position `pred` such that `pred <= pos` and the `pred`-th bit is unset, or
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
    /// It panics if the index is not built by [`Self::enable_rank()`] and [`Self::enable_select0()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{DArray, Predecessor};
    ///
    /// let da = DArray::from_bits([true, false, true, false]).enable_rank().enable_select0();
    ///
    /// assert_eq!(da.predecessor0(3), Some(3));
    /// assert_eq!(da.predecessor0(2), Some(1));
    /// assert_eq!(da.predecessor0(1), Some(1));
    /// assert_eq!(da.predecessor0(0), None);
    /// ```
    fn predecessor0(&self, pos: usize) -> Option<usize> {
        self.r9.as_ref().expect("enable_rank() must be set up.");
        self.s0.as_ref().expect("enable_select0() must be set up.");
        if self.len() <= pos {
            return None;
        }
        let k = self.rank0(pos + 1).unwrap();
        (k != 0).then(|| self.select0(k - 1).unwrap())
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

    /// Returns the smallest bit position `succ` such that `succ >= pos` and the `succ`-th bit is unset, or
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
    /// It panics if the index is not built by [`Self::enable_rank()`] and [`Self::enable_select0()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{DArray, Successor};
    ///
    /// let da = DArray::from_bits([false, true, false, true]).enable_rank().enable_select0();
    ///
    /// assert_eq!(da.successor0(0), Some(0));
    /// assert_eq!(da.successor0(1), Some(2));
    /// assert_eq!(da.successor0(2), Some(2));
    /// assert_eq!(da.successor0(3), None);
    /// ```
    fn successor0(&self, pos: usize) -> Option<usize> {
        self.r9.as_ref().expect("enable_rank() must be set up.");
        self.s0.as_ref().expect("enable_select0() must be set up.");
        if self.len() <= pos {
            return None;
        }
        let k = self.rank0(pos).unwrap();
        (k < self.num_zeros()).then(|| self.select0(k).unwrap())
    }
}

impl Serializable for DArray {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.bv.serialize_into(&mut writer)?;
        mem += self.s1.serialize_into(&mut writer)?;
        mem += self.s0.serialize_into(&mut writer)?;
        mem += self.r9.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let bv = BitVector::deserialize_from(&mut reader)?;
        let s1 = DArrayIndex::deserialize_from(&mut reader)?;
        let s0 = Option::<DArrayIndex>::deserialize_from(&mut reader)?;
        let r9 = Option::<Rank9SelIndex>::deserialize_from(&mut reader)?;
        Ok(Self { bv, s1, s0, r9 })
    }

    fn size_in_bytes(&self) -> usize {
        self.bv.size_in_bytes()
            + self.s1.size_in_bytes()
            + self.s0.size_in_bytes()
            + self.r9.size_in_bytes()
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
