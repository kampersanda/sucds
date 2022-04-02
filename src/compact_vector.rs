//! Compact vector in which each integer is represented in a fixed number of bits.
#![cfg(target_pointer_width = "64")]

pub mod iter;

use std::io::{Read, Write};
use std::mem::size_of;

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use crate::compact_vector::iter::Iter;
use crate::{util, BitVector};

/// Compact vector in which each integer is represented in a fixed number of bits.
///
/// # Examples
///
/// ```
/// use sucds::CompactVector;
///
/// let cv = CompactVector::from_slice(&[5, 256, 0, 10]);
///
/// assert_eq!(cv.get(0), 5);
/// assert_eq!(cv.get(1), 256);
/// assert_eq!(cv.get(2), 0);
/// assert_eq!(cv.get(3), 10);
///
/// assert_eq!(cv.len(), 4);
/// assert_eq!(cv.width(), 9);
///
/// let mut bytes = vec![];
/// let size = cv.serialize_into(&mut bytes).unwrap();
/// let other = CompactVector::deserialize_from(&bytes[..]).unwrap();
/// assert_eq!(cv, other);
/// assert_eq!(size, bytes.len());
/// assert_eq!(size, cv.size_in_bytes());
/// ```
#[derive(Default, Clone, PartialEq, Eq)]
pub struct CompactVector {
    chunks: BitVector,
    len: usize,
    width: usize,
}

impl CompactVector {
    /// Creates a new empty [`CompactVector`].
    ///
    /// # Arguments
    ///
    /// - `width`: Number of bits to represent an integer.
    pub fn new(width: usize) -> Self {
        Self {
            chunks: BitVector::default(),
            len: 0,
            width,
        }
    }

    /// Creates a new [`CompactVector`] of `len` integers.
    ///
    /// # Arguments
    ///
    /// - `len`: Number of integers to be stored.
    /// - `width`: Number of bits to represent an integer.
    pub fn with_len(len: usize, width: usize) -> Self {
        Self {
            chunks: BitVector::with_len(len * width),
            len,
            width,
        }
    }

    /// Creates a new [`CompactVector`] that `capa` integers are reserved.
    ///
    /// # Arguments
    ///
    /// - `capa`: Number of integers to be reserved.
    /// - `width`: Number of bits to represent an integer.
    pub fn with_capacity(capa: usize, width: usize) -> Self {
        Self {
            chunks: BitVector::with_capacity(capa * width),
            len: 0,
            width,
        }
    }

    /// Creates a new [`CompactVector`] from a slice of integers.
    ///
    /// # Arguments
    ///
    /// - `ints`: Integers to be stored.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::CompactVector;
    ///
    /// let cv = CompactVector::from_slice(&[5, 256, 0, 10]);
    /// assert_eq!(cv.get(0), 5);
    /// assert_eq!(cv.get(1), 256);
    /// assert_eq!(cv.get(2), 0);
    /// assert_eq!(cv.get(3), 10);
    /// ```
    pub fn from_slice(ints: &[usize]) -> Self {
        let &max_int = ints.iter().max().unwrap();
        let mut cv = Self::with_len(ints.len(), util::needed_bits(max_int));
        for (i, &x) in ints.iter().enumerate() {
            cv.set(i, x);
        }
        cv
    }

    /// Serializes the data structure into the writer,
    /// returning the number of serialized bytes.
    ///
    /// # Arguments
    ///
    /// - `writer`: `std::io::Write` variable.
    pub fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mem = self.chunks.serialize_into(&mut writer)?;
        writer.write_u64::<LittleEndian>(self.len as u64)?;
        writer.write_u64::<LittleEndian>(self.width as u64)?;
        Ok(mem + (size_of::<u64>() * 2))
    }

    /// Deserializes the data structure from the reader.
    ///
    /// # Arguments
    ///
    /// - `reader`: `std::io::Read` variable.
    pub fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let chunks = BitVector::deserialize_from(&mut reader)?;
        let len = reader.read_u64::<LittleEndian>()? as usize;
        let width = reader.read_u64::<LittleEndian>()? as usize;
        Ok(Self { chunks, len, width })
    }

    /// Returns the number of bytes to serialize the data structure.
    pub fn size_in_bytes(&self) -> usize {
        self.chunks.size_in_bytes() + (size_of::<u64>() * 2)
    }

    /// Gets the `pos`-th integer.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::CompactVector;
    ///
    /// let cv = CompactVector::from_slice(&[5, 256, 0, 10]);
    /// assert_eq!(cv.get(0), 5);
    /// assert_eq!(cv.get(1), 256);
    /// assert_eq!(cv.get(2), 0);
    /// assert_eq!(cv.get(3), 10);
    /// ```
    #[inline(always)]
    pub fn get(&self, pos: usize) -> usize {
        self.chunks.get_bits(pos * self.width, self.width)
    }

    /// Sets the `pos`-th integer to `value`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position.
    /// - `value`: Integer to be set.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::CompactVector;
    ///
    /// let mut cv = CompactVector::with_len(2, 8);
    /// cv.set(0, 10);
    /// cv.set(1, 255);
    /// assert_eq!(cv.get(0), 10);
    /// assert_eq!(cv.get(1), 255);
    /// ```
    #[inline(always)]
    pub fn set(&mut self, pos: usize, value: usize) {
        self.chunks.set_bits(pos * self.width, value, self.width);
    }

    /// Pushes integer `value` at the end.
    ///
    /// # Arguments
    ///
    /// - `value`: Integer to be set.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::CompactVector;
    ///
    /// let mut cv = CompactVector::new(8);
    /// cv.push(10);
    /// cv.push(255);
    /// assert_eq!(cv.get(0), 10);
    /// assert_eq!(cv.get(1), 255);
    /// ```
    #[inline(always)]
    pub fn push(&mut self, value: usize) {
        self.chunks.push_bits(value, self.width);
        self.len += 1;
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

impl std::fmt::Debug for CompactVector {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut ints = vec![0; self.len()];
        for (i, b) in ints.iter_mut().enumerate() {
            *b = self.get(i);
        }
        f.debug_struct("CompactVector")
            .field("ints", &ints)
            .field("len", &self.len)
            .field("width", &self.width)
            .finish()
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
            assert_eq!(x, list.get(i));
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
            let list = CompactVector::from_slice(&ints);
            test_basic(&ints, &list);
        }
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let cv = CompactVector::from_slice(&gen_random_ints(10000, 42));
        let size = cv.serialize_into(&mut bytes).unwrap();
        let other = CompactVector::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(cv, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, cv.size_in_bytes());
    }
}
