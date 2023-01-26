//! Compact vector in which each integer is represented in a fixed number of bits.
#![cfg(target_pointer_width = "64")]

pub mod iter;

use std::io::{Read, Write};

use anyhow::{anyhow, Result};
use num_traits::ToPrimitive;

use crate::compact_vector::iter::Iter;
use crate::{util, BitVector, IntGetter, Searial};

/// Compact vector in which each integer is represented in a fixed number of bits.
///
/// # Examples
///
/// ```
/// use sucds::{CompactVector, IntGetter};
///
/// let cv = CompactVector::from_slice(&[5, 256, 0, 10]);
///
/// assert_eq!(cv.get_int(0), Some(5));
/// assert_eq!(cv.get_int(1), Some(256));
/// assert_eq!(cv.get_int(2), Some(0));
/// assert_eq!(cv.get_int(3), Some(10));
///
/// assert_eq!(cv.len(), 4);
/// assert_eq!(cv.width(), 9);
/// ```
#[derive(Default, Clone, PartialEq, Eq)]
pub struct CompactVector {
    chunks: BitVector,
    len: usize,
    width: usize,
}

impl CompactVector {
    fn verify_width(width: usize) -> Result<()> {
        if 0 < width && width <= 64 {
            Ok(())
        } else {
            Err(anyhow!("width must be in 1..=64."))
        }
    }

    /// Creates a new empty vector storing an integer in `width` bits.
    ///
    /// # Errors
    ///
    /// An error is returned if `width` is not in `1..=64`.
    pub fn new(width: usize) -> Result<Self> {
        Self::verify_width(width)?;
        Ok(Self {
            chunks: BitVector::default(),
            len: 0,
            width,
        })
    }

    /// Creates a new vector storing an integer in `width` bits,
    /// which at least `capa` integers are reserved.
    ///
    /// # Errors
    ///
    /// An error is returned if `width` is not in `1..=64`.
    pub fn with_capacity(capa: usize, width: usize) -> Result<Self> {
        Self::verify_width(width)?;
        Ok(Self {
            chunks: BitVector::with_capacity(capa * width),
            len: 0,
            width,
        })
    }

    /// Creates a new vector storing an integer in `width` bits,
    /// which stores `len` values initialized by `val`.
    ///
    /// # Errors
    ///
    /// An error is returned if `width` is not in `1..=64`.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::BitVector;
    ///
    /// let bv = BitVector::from_bit(false, 5);
    /// assert_eq!(bv.len(), 5);
    /// ```
    pub fn from_int(val: usize, len: usize, width: usize) -> Result<Self> {
        let mut cv = Self::with_capacity(len, width)?;
        for _ in 0..len {
            cv.push_int(val)?;
        }
        Ok(cv)
    }

    /// Creates a new vector from a slice of integers `vals`.
    ///
    /// The width of each element automatically fits to the maximum value in `vals`.
    ///
    /// # Errors
    ///
    /// An error is returned if `vals` contains an integer that cannot be cast to `usize`.
    pub fn from_slice<T>(vals: &[T]) -> Result<Self>
    where
        T: ToPrimitive,
    {
        if vals.is_empty() {
            return Ok(Self::default());
        }
        let mut max_int = 0;
        for x in vals {
            max_int = max_int.max(x.to_usize().ok_or(anyhow!(
                "vals must consist only of values castable into usize."
            ))?);
        }
        let mut cv = Self::with_capacity(vals.len(), util::needed_bits(max_int))?;
        for x in vals {
            // Casting and pushing should be safe.
            cv.push_int(x.to_usize().unwrap()).unwrap();
        }
        Ok(cv)
    }

    /// Sets the `pos`-th integer to `val`.
    ///
    /// # Errors
    ///
    /// An error is returned if
    ///
    /// - `pos` is out of bounds, or
    /// - `val` cannot be represent in `self.width()` bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::CompactVector;
    ///
    /// let mut cv = CompactVector::with_len(2, 8);
    /// assert!(cv.set_int(0, 10).is_ok());
    /// assert!(cv.set_int(1, 255).is_ok());
    /// ```
    #[inline(always)]
    pub fn set_int(&mut self, pos: usize, val: usize) -> Result<()> {
        self.chunks.set_bits(pos * self.width, val, self.width)
    }

    /// Pushes integer `val` at the end.
    ///
    /// # Errors
    ///
    /// An error is returned if `val` cannot be represent in `self.width()` bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::CompactVector;
    ///
    /// let mut cv = CompactVector::new(8);
    /// assert!(cv.push_int(255).is_ok());
    /// assert!(cv.push_int(256).is_err());
    /// ```
    #[inline(always)]
    pub fn push_int(&mut self, val: usize) -> Result<()> {
        self.chunks.push_bits(val, self.width)?;
        self.len += 1;
        Ok(())
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::CompactVector;
    ///
    /// let cv = CompactVector::from_slice(&[5, 256, 0, 10]);
    /// let mut it = cv.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(256));
    /// assert_eq!(it.next(), Some(0));
    /// assert_eq!(it.next(), Some(10));
    /// assert_eq!(it.next(), None);
    /// ```
    pub const fn iter(&self) -> Iter {
        Iter::new(self)
    }

    /// Gets the number of ints.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of bits to represent an integer.
    #[inline(always)]
    pub const fn width(&self) -> usize {
        self.width
    }
}

impl IntGetter for CompactVector {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{CompactVector, IntGetter};
    ///
    /// let cv = CompactVector::from_slice(&[5, 256, 0]);
    /// assert_eq!(cv.get_int(0), Some(5));
    /// assert_eq!(cv.get_int(1), Some(256));
    /// assert_eq!(cv.get_int(2), Some(0));
    /// assert_eq!(cv.get_int(3), None);
    fn get_int(&self, pos: usize) -> Option<usize> {
        self.chunks.get_bits(pos * self.width, self.width)
    }
}

impl std::fmt::Debug for CompactVector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ints = vec![0; self.len()];
        for (i, b) in ints.iter_mut().enumerate() {
            *b = self.get_int(i).unwrap();
        }
        f.debug_struct("CompactVector")
            .field("ints", &ints)
            .field("len", &self.len)
            .field("width", &self.width)
            .finish()
    }
}

impl Searial for CompactVector {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = self.chunks.serialize_into(&mut writer)?;
        mem += self.len.serialize_into(&mut writer)?;
        mem += self.width.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let chunks = BitVector::deserialize_from(&mut reader)?;
        let len = usize::deserialize_from(&mut reader)?;
        let width = usize::deserialize_from(&mut reader)?;
        Ok(Self { chunks, len, width })
    }

    fn size_in_bytes(&self) -> usize {
        self.chunks.size_in_bytes() + usize::size_of().unwrap() * 2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn gen_random_ints(len: usize, seed: u64) -> Vec<usize> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen_range(0..10000)).collect()
    }

    fn test_basic(ints: &[usize], list: &CompactVector) {
        for (i, &x) in ints.iter().enumerate() {
            assert_eq!(x, list.get_int(i).unwrap());
        }
        for (i, x) in list.iter().enumerate() {
            assert_eq!(ints[i], x);
        }
        assert_eq!(ints.len(), list.len());
    }

    #[test]
    fn test_random_ints() {
        for seed in 0..100 {
            let ints = gen_random_ints(10000, seed);
            let list = CompactVector::from_slice(&ints).unwrap();
            test_basic(&ints, &list);
        }
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let cv = CompactVector::from_slice(&gen_random_ints(10000, 42)).unwrap();
        let size = cv.serialize_into(&mut bytes).unwrap();
        let other = CompactVector::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(cv, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, cv.size_in_bytes());
    }
}
