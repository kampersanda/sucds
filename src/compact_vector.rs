//! Compact vector in which each integer is represented in a fixed number of bits.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};

use anyhow::{anyhow, Result};
use num_traits::ToPrimitive;

use crate::{util, BitVector, IntGetter, Searial};

/// Compact vector in which each integer is represented in a fixed number of bits.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use sucds::{CompactVector, IntGetter};
///
/// // Can store integers within 3 bits each.
/// let mut cv = CompactVector::new(3)?;
///
/// cv.push_int(7)?;
/// cv.push_int(2)?;
///
/// assert_eq!(cv.len(), 2);
/// assert_eq!(cv.get_int(0), Some(7)); // Need IntGetter
///
/// cv.set_int(0, 5)?;
/// assert_eq!(cv.get_int(0), Some(5));
/// # Ok(())
/// # }
/// ```
#[derive(Default, Clone, PartialEq, Eq)]
pub struct CompactVector {
    chunks: BitVector,
    len: usize,
    width: usize,
}

impl CompactVector {
    /// Creates a new empty vector storing integers within `width` bits each.
    ///
    /// # Arguments
    ///
    ///  - `width`: Number of bits used to store an integer.
    ///
    /// # Errors
    ///
    /// An error is returned if `width` is not in `1..=64`.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::CompactVector;
    ///
    /// let mut cv = CompactVector::new(3)?;
    /// assert_eq!(cv.len(), 0);
    /// assert_eq!(cv.width(), 3);
    /// # Ok(())
    /// # }
    /// ```
    pub fn new(width: usize) -> Result<Self> {
        if !(0..=64).contains(&width) {
            return Err(anyhow!("width must be in 1..=64."));
        }
        Ok(Self {
            chunks: BitVector::default(),
            len: 0,
            width,
        })
    }

    /// Creates a new vector storing an integer in `width` bits,
    /// where space for storing at least `capa` integers is reserved.
    ///
    /// # Arguments
    ///
    ///  - `capa`: Number of elements reserved at least.
    ///  - `width`: Number of bits used to store an integer.
    ///
    /// # Errors
    ///
    /// An error is returned if `width` is not in `1..=64`.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::CompactVector;
    ///
    /// let mut cv = CompactVector::with_capacity(10, 3)?;
    ///
    /// assert_eq!(cv.len(), 0);
    /// assert_eq!(cv.width(), 3);
    ///
    /// // Space for storing 21 integers is reserved due to the data structure.
    /// assert_eq!(cv.capacity(), 21);
    /// # Ok(())
    /// # }
    /// ```
    pub fn with_capacity(capa: usize, width: usize) -> Result<Self> {
        if !(0..=64).contains(&width) {
            return Err(anyhow!("width must be in 1..=64."));
        }
        Ok(Self {
            chunks: BitVector::with_capacity(capa * width),
            len: 0,
            width,
        })
    }

    /// Creates a new vector storing an integer in `width` bits,
    /// which stores `len` values initialized by `val`.
    ///
    /// # Arguments
    ///
    ///  - `val`: Integer value.
    ///  - `len`: Number of elements.
    ///  - `width`: Number of bits used to store an integer.
    ///
    /// # Errors
    ///
    /// An error is returned if
    ///
    ///  - `width` is not in `1..=64`, or
    ///  - `val` cannot be represent in `width` bits.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::{CompactVector, IntGetter};
    ///
    /// let mut cv = CompactVector::from_int(7, 2, 3)?;
    /// assert_eq!(cv.len(), 2);
    /// assert_eq!(cv.width(), 3);
    /// assert_eq!(cv.get_int(0), Some(7));
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_int(val: usize, len: usize, width: usize) -> Result<Self> {
        if !(0..=64).contains(&width) {
            return Err(anyhow!("width must be in 1..=64."));
        }
        if val >> width != 0 {
            return Err(anyhow!(
                "val must fit in width={width} bits, but got {val}."
            ));
        }
        // NOTE(kampersanda): It should be safe.
        let mut cv = Self::with_capacity(len, width).unwrap();
        for _ in 0..len {
            // NOTE(kampersanda): It should be safe.
            cv.push_int(val).unwrap();
        }
        Ok(cv)
    }

    /// Creates a new vector from a slice of integers `vals`.
    ///
    /// The width of each element automatically fits to the maximum value in `vals`.
    ///
    /// # Arguments
    ///
    ///  - `vals`: Slice of integers to be stored.
    ///
    /// # Errors
    ///
    /// An error is returned if `vals` contains an integer that cannot be cast to [`usize`].
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::{CompactVector, IntGetter};
    ///
    /// let mut cv = CompactVector::from_slice(&[7, 2])?;
    /// assert_eq!(cv.len(), 2);
    /// assert_eq!(cv.width(), 3);
    /// assert_eq!(cv.get_int(0), Some(7));
    /// # Ok(())
    /// # }
    /// ```
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
    /// # Arguments
    ///
    ///  - `pos`: Position.
    ///  - `val`: Integer value set.
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
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::{CompactVector, IntGetter};
    ///
    /// let mut cv = CompactVector::from_int(0, 2, 3)?;
    /// cv.set_int(1, 4)?;
    /// assert_eq!(cv.get_int(1), Some(4));
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn set_int(&mut self, pos: usize, val: usize) -> Result<()> {
        if self.len() <= pos {
            return Err(anyhow!(
                "pos must be no greater than self.len()={}, but got {pos}.",
                self.len()
            ));
        }
        if val >> self.width() != 0 {
            return Err(anyhow!(
                "val must fit in self.width()={} bits, but got {val}.",
                self.width()
            ));
        }
        // NOTE(kampersanda): set_bits should be safe.
        Ok(self
            .chunks
            .set_bits(pos * self.width, val, self.width)
            .unwrap())
    }

    /// Pushes integer `val` at the end.
    ///
    /// # Arguments
    ///
    ///  - `val`: Integer value pushed.
    ///
    /// # Errors
    ///
    /// An error is returned if `val` cannot be represent in `self.width()` bits.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::CompactVector;
    ///
    /// let mut cv = CompactVector::new(3)?;
    /// cv.push_int(2)?;
    /// cv.push_int(1)?;
    /// assert_eq!(cv.len(), 2);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn push_int(&mut self, val: usize) -> Result<()> {
        if val >> self.width() != 0 {
            return Err(anyhow!(
                "val must fit in self.width()={} bits, but got {val}.",
                self.width()
            ));
        }
        // NOTE(kampersanda): set_bits should be safe.
        self.chunks.push_bits(val, self.width).unwrap();
        self.len += 1;
        Ok(())
    }

    /// Appends integers at the end.
    ///
    /// # Arguments
    ///
    ///  - `vals`: Integer stream to be pushed.
    ///
    /// # Errors
    ///
    /// An error is returned if values in `vals` cannot be represent in `self.width()` bits.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::CompactVector;
    ///
    /// let mut cv = CompactVector::new(3)?;
    /// cv.extend([2, 1, 3])?;
    /// assert_eq!(cv.len(), 3);
    /// # Ok(())
    /// # }
    /// ```
    pub fn extend<'a, I>(&mut self, vals: I) -> Result<()>
    where
        I: IntoIterator<Item = usize>,
    {
        for x in vals {
            self.push_int(x)?;
        }
        Ok(())
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::CompactVector;
    ///
    /// let cv = CompactVector::from_slice(&[5, 256, 0])?;
    /// let mut it = cv.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(256));
    /// assert_eq!(it.next(), Some(0));
    /// assert_eq!(it.next(), None);
    /// # Ok(())
    /// # }
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

    /// Returns the total number of bits it can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.chunks.capacity() / self.width()
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
    /// # Arguments
    ///
    ///  - `pos`: Position.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::{CompactVector, IntGetter};
    ///
    /// let cv = CompactVector::from_slice(&[5, 256, 0])?;
    /// assert_eq!(cv.get_int(0), Some(5));
    /// assert_eq!(cv.get_int(1), Some(256));
    /// assert_eq!(cv.get_int(2), Some(0));
    /// assert_eq!(cv.get_int(3), None);
    /// # Ok(())
    /// # }
    fn get_int(&self, pos: usize) -> Option<usize> {
        self.chunks.get_bits(pos * self.width, self.width)
    }
}

/// Iterator for enumerating integers, created by [`CompactVector::iter()`].
pub struct Iter<'a> {
    cv: &'a CompactVector,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(cv: &'a CompactVector) -> Self {
        Self { cv, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.cv.len() {
            let x = self.cv.get_int(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.cv.len(), Some(self.cv.len()))
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

    #[test]
    fn test_new_oob() {
        let e = CompactVector::new(65);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("width must be in 1..=64.".to_string())
        );
    }

    #[test]
    fn test_with_capacity_oob() {
        let e = CompactVector::with_capacity(0, 65);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("width must be in 1..=64.".to_string())
        );
    }

    #[test]
    fn test_from_int_oob() {
        let e = CompactVector::from_int(0, 0, 65);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("width must be in 1..=64.".to_string())
        );
    }

    #[test]
    fn test_from_int_unfit() {
        let e = CompactVector::from_int(4, 0, 2);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("val must fit in width=2 bits, but got 4.".to_string())
        );
    }

    #[test]
    fn test_from_slice_uncastable() {
        let e = CompactVector::from_slice(&[u128::MAX]);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("vals must consist only of values castable into usize.".to_string())
        );
    }

    #[test]
    fn test_set_int_oob() {
        let mut cv = CompactVector::from_int(0, 1, 2).unwrap();
        let e = cv.set_int(1, 1);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("pos must be no greater than self.len()=1, but got 1.".to_string())
        );
    }

    #[test]
    fn test_set_int_unfit() {
        let mut cv = CompactVector::from_int(0, 1, 2).unwrap();
        let e = cv.set_int(0, 4);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("val must fit in self.width()=2 bits, but got 4.".to_string())
        );
    }

    #[test]
    fn test_push_int_unfit() {
        let mut cv = CompactVector::new(2).unwrap();
        let e = cv.push_int(4);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("val must fit in self.width()=2 bits, but got 4.".to_string())
        );
    }

    #[test]
    fn test_extend_unfit() {
        let mut cv = CompactVector::new(2).unwrap();
        let e = cv.extend([4]);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("val must fit in self.width()=2 bits, but got 4.".to_string())
        );
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let cv = CompactVector::from_slice(&[7, 334, 1, 2]).unwrap();
        let size = cv.serialize_into(&mut bytes).unwrap();
        let other = CompactVector::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(cv, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, cv.size_in_bytes());
    }
}
