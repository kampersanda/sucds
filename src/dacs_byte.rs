//! Compressed integer array using Directly Addressable Codes (DACs) in a simple bytewise scheme.
#![cfg(target_pointer_width = "64")]

use std::convert::TryFrom;
use std::io::{Read, Write};

use anyhow::Result;

use crate::util;
use crate::{BitVector, RsBitVector, Searial};

const LEVEL_WIDTH: usize = 8;
const LEVEL_MASK: usize = (1 << LEVEL_WIDTH) - 1;

/// Compressed integer array using Directly Addressable Codes (DACs) in a simple bytewise scheme.
///
/// DACs are a compact representation of an integer array consisting of many small values.
/// [`DacsByte`] is a simple variant and uses [`Vec<u8>`] for each level to obtain faster
/// operations than [`DacsOpt`](crate::DacsOpt).
///
/// # Examples
///
/// ```
/// use sucds::DacsByte;
///
/// let list = DacsByte::from_slice(&[5, 0, 100000, 334]);
///
/// assert_eq!(list.get(0), 5);
/// assert_eq!(list.get(1), 0);
/// assert_eq!(list.get(2), 100000);
/// assert_eq!(list.get(3), 334);
///
/// assert_eq!(list.len(), 4);
/// assert_eq!(list.num_levels(), 3);
/// ```
///
/// # References
///
/// - N. R. Brisaboa, S. Ladra, and G. Navarro, "DACs: Bringing direct access to variable-length
///   codes." Information Processing & Management, 49(1), 392-404, 2013.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DacsByte {
    data: Vec<Vec<u8>>,
    flags: Vec<RsBitVector>,
}

impl DacsByte {
    /// Builds DACs by assigning 8 bits to represent each level.
    ///
    /// # Arguments
    ///
    /// - `ints`: Integers to be stored.
    pub fn from_slice(ints: &[usize]) -> Self {
        if ints.is_empty() {
            return Self::default();
        }

        let num_bits = util::needed_bits(ints.iter().cloned().max().unwrap());
        let num_levels = util::ceiled_divide(num_bits, LEVEL_WIDTH);
        assert_ne!(num_levels, 0);

        if num_levels == 1 {
            let data: Vec<_> = ints.iter().map(|&x| u8::try_from(x).unwrap()).collect();
            return Self {
                data: vec![data],
                flags: vec![],
            };
        }

        let mut data = vec![vec![]; num_levels];
        let mut flags = vec![BitVector::default(); num_levels - 1];

        for mut x in ints.iter().cloned() {
            for j in 0..num_levels {
                data[j].push(u8::try_from(x & LEVEL_MASK).unwrap());
                x >>= LEVEL_WIDTH;
                if j == num_levels - 1 {
                    assert_eq!(x, 0);
                    break;
                } else if x == 0 {
                    flags[j].push_bit(false);
                    break;
                }
                flags[j].push_bit(true);
            }
        }

        let flags = flags.into_iter().map(RsBitVector::new).collect();
        Self { data, flags }
    }

    /// Gets the `pos`-th integer.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position to get.
    ///
    /// # Complexity
    ///
    /// - $`O( \ell_{pos} )`$ where $`\ell_{pos}`$ is the number of levels corresponding to
    ///   the `pos`-th integer.
    pub fn get(&self, mut pos: usize) -> usize {
        let mut x = 0;
        for j in 0..self.num_levels() {
            x |= usize::from(self.data[j][pos]) << (j * LEVEL_WIDTH);
            if j == self.num_levels() - 1 || !self.flags[j].get_bit(pos) {
                break;
            }
            pos = self.flags[j].rank1(pos);
        }
        x
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::DacsByte;
    ///
    /// let list = DacsByte::from_slice(&[5, 0, 100000, 334]);
    /// let mut it = list.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(0));
    /// assert_eq!(it.next(), Some(100000));
    /// assert_eq!(it.next(), Some(334));
    /// assert_eq!(it.next(), None);
    /// ```
    pub const fn iter(&self) -> Iter {
        Iter::new(self)
    }

    /// Gets the number of bits.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.data[0].len()
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of levels.
    #[inline(always)]
    pub fn num_levels(&self) -> usize {
        self.data.len()
    }

    /// Gets the number of bits for each level.
    #[inline(always)]
    pub fn widths(&self) -> Vec<usize> {
        self.data.iter().map(|_| LEVEL_WIDTH).collect()
    }
}

impl Default for DacsByte {
    fn default() -> Self {
        Self {
            // Needs a single level at least.
            data: vec![vec![]],
            flags: vec![],
        }
    }
}

/// Iterator for enumerating integers, created by [`DacsByte::iter()`].
pub struct Iter<'a> {
    list: &'a DacsByte,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(list: &'a DacsByte) -> Self {
        Self { list, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.list.len() {
            let x = self.list.get(self.pos);
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len(), Some(self.list.len()))
    }
}

impl Searial for DacsByte {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.data.serialize_into(&mut writer)?;
        mem += self.flags.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let data = Vec::<Vec<u8>>::deserialize_from(&mut reader)?;
        let flags = Vec::<RsBitVector>::deserialize_from(&mut reader)?;
        Ok(Self { data, flags })
    }

    fn size_in_bytes(&self) -> usize {
        self.data.size_in_bytes() + self.flags.size_in_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        let list = DacsByte::from_slice(&[0xFFFF, 0xFF, 0xF, 0xFFFFF, 0xF]);

        assert_eq!(
            list.data,
            vec![
                vec![0xFF, 0xFF, 0xF, 0xFF, 0xF],
                vec![0xFF, 0xFF],
                vec![0xF]
            ]
        );

        assert_eq!(
            list.flags,
            vec![
                RsBitVector::from_bits([true, false, false, true, false]),
                RsBitVector::from_bits([false, true])
            ]
        );

        assert!(!list.is_empty());
        assert_eq!(list.len(), 5);
        assert_eq!(list.num_levels(), 3);
        assert_eq!(list.widths(), vec![LEVEL_WIDTH, LEVEL_WIDTH, LEVEL_WIDTH]);

        assert_eq!(list.get(0), 0xFFFF);
        assert_eq!(list.get(1), 0xFF);
        assert_eq!(list.get(2), 0xF);
        assert_eq!(list.get(3), 0xFFFFF);
        assert_eq!(list.get(4), 0xF);
    }

    #[test]
    fn test_empty() {
        let list = DacsByte::from_slice(&[]);
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert_eq!(list.num_levels(), 1);
        assert_eq!(list.widths(), vec![LEVEL_WIDTH]);
    }

    #[test]
    fn test_all_zeros() {
        let list = DacsByte::from_slice(&[0, 0, 0, 0]);
        assert!(!list.is_empty());
        assert_eq!(list.len(), 4);
        assert_eq!(list.num_levels(), 1);
        assert_eq!(list.widths(), vec![LEVEL_WIDTH]);
        assert_eq!(list.get(0), 0);
        assert_eq!(list.get(1), 0);
        assert_eq!(list.get(2), 0);
        assert_eq!(list.get(3), 0);
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let list = DacsByte::from_slice(&[0xFFFFF, 0xFF, 0xF, 0xFFFFF, 0xF]);
        let size = list.serialize_into(&mut bytes).unwrap();
        let other = DacsByte::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(list, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, list.size_in_bytes());
    }
}
