//! Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
#![cfg(target_pointer_width = "64")]

pub mod inner;

use std::io::{Read, Write};

use anyhow::Result;

use crate::{BitVector, Searial, Selector};
use inner::DArrayIndex;

/// Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
///
/// This is a yet another Rust port of [succinct::darray](https://github.com/ot/succinct/blob/master/darray.hpp).
///
/// # Examples
///
/// ```
/// use sucds::{DArray, Selector};
///
/// let da = DArray::from_bits([true, false, false, true]);
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
        Self {
            da: DArrayIndex::new(&bv, true),
            bv,
        }
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

    /// Gets the reference of the internal bit vector.
    pub const fn bit_vector(&self) -> &BitVector {
        &self.bv
    }

    /// Gets the reference of the internal select index.
    pub const fn da_index(&self) -> &DArrayIndex {
        &self.da
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

/// Iterator for enumerating integers, created by [`DArray::iter()`].
pub struct Iter<'a> {
    da: &'a DArray,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(da: &'a DArray) -> Self {
        Self { da, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.da.len() {
            let x = self.da.select1(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.da.len(), Some(self.da.len()))
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
    fn test_select1() {
        let da = DArray::from_bits([false, true, false]);
        da.select0(0);
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
