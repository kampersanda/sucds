//! Compressed integer sequence using Directly Addressable Codes (DACs) in a simple bytewise scheme.
#![cfg(target_pointer_width = "64")]

use std::convert::TryFrom;
use std::io::{Read, Write};

use anyhow::Result;

use crate::bit_vectors::{self, BitVector, Rank, Rank9Sel};
use crate::int_vectors::{Access, Build, NumVals};
use crate::utils;
use crate::Serializable;

const LEVEL_WIDTH: usize = 8;
const LEVEL_MASK: usize = (1 << LEVEL_WIDTH) - 1;

/// Compressed integer sequence using Directly Addressable Codes (DACs) in a simple bytewise scheme.
///
/// DACs are a compact representation of an integer sequence consisting of many small values.
/// [`DacsByte`] is a simple variant and uses [`Vec<u8>`] for each level to obtain faster
/// operations than [`DacsOpt`](super::DacsOpt).
///
/// # Memory complexity
///
/// $`\textrm{DAC}(A) + o(\textrm{DAC}(A)/b) + O(\lg u)`$ bits where
///
/// - $`u`$ is the maximum value plus 1,
/// - $`b`$ is the length in bits assigned for each level with DACs (here $`b = 8`$), and
/// - $`\textrm{DAC}(A)`$ is the length in bits of the encoded sequence from an original sequence $`A`$ with DACs.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use sucds::int_vectors::{DacsByte, Access};
///
/// let seq = DacsByte::from_slice(&[5, 0, 100000, 334])?;
///
/// assert_eq!(seq.access(0), Some(5));
/// assert_eq!(seq.access(1), Some(0));
/// assert_eq!(seq.access(2), Some(100000));
/// assert_eq!(seq.access(3), Some(334));
///
/// assert_eq!(seq.len(), 4);
/// assert_eq!(seq.num_levels(), 3);
/// # Ok(())
/// # }
/// ```
///
/// # References
///
/// - N. R. Brisaboa, S. Ladra, and G. Navarro, "DACs: Bringing direct access to variable-length
///   codes." Information Processing & Management, 49(1), 392-404, 2013.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DacsByte {
    data: Vec<Vec<u8>>,
    flags: Vec<Rank9Sel>,
}

impl DacsByte {
    /// Builds DACs by assigning 8 bits to represent each level.
    ///
    /// # Arguments
    ///
    /// - `vals`: Slice of integers to be stored.
    ///
    pub fn from_slice<T>(vals: &[T]) -> Self
    where
        T: Into<usize> + Copy,
    {
        if vals.is_empty() {
            return Self::default();
        }

        let mut maxv = 0;
        for x in vals {
            maxv = maxv.max((*x).into());
        }
        let num_bits = utils::needed_bits(maxv.into());
        let num_levels = utils::ceiled_divide(num_bits, LEVEL_WIDTH);
        assert_ne!(num_levels, 0);

        if num_levels == 1 {
            let data: Vec<_> = vals
                .iter()
                .map(|x| u8::try_from((*x).into()).unwrap())
                .collect();
            return Self {
                data: vec![data],
                flags: vec![],
            };
        }

        let mut data = vec![vec![]; num_levels];
        let mut flags = vec![BitVector::default(); num_levels - 1];

        for x in vals {
            let mut x = (*x).into();
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

        let flags = flags.into_iter().map(Rank9Sel::new).collect();
        Self { data, flags }
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::int_vectors::DacsByte;
    ///
    /// let seq = DacsByte::from_slice(&[5, 0, 100000, 334])?;
    /// let mut it = seq.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(0));
    /// assert_eq!(it.next(), Some(100000));
    /// assert_eq!(it.next(), Some(334));
    /// assert_eq!(it.next(), None);
    /// # Ok(())
    /// # }
    /// ```
    pub const fn iter(&self) -> Iter {
        Iter::new(self)
    }

    /// Gets the number of integers.
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

impl Build for DacsByte {
    /// Creates a new vector from a slice of integers `vals`.
    ///
    /// This just calls [`Self::from_slice()`]. See the documentation.
    fn build_from_slice<T>(vals: &[T]) -> Self
    where
        T: Into<usize> + Copy,
        Self: Sized,
    {
        Self::from_slice(vals)
    }
}

impl NumVals for DacsByte {
    /// Returns the number of integers stored (just wrapping [`Self::len()`]).
    fn num_vals(&self) -> usize {
        self.len()
    }
}

impl Access for DacsByte {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// $`O( \ell_{pos} )`$ where $`\ell_{pos}`$ is the number of levels corresponding to
    /// the `pos`-th integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::int_vectors::{DacsByte, Access};
    ///
    /// let seq = DacsByte::from_slice(&[5, 999, 334]);
    ///
    /// assert_eq!(seq.access(0), Some(5));
    /// assert_eq!(seq.access(1), Some(999));
    /// assert_eq!(seq.access(2), Some(334));
    /// assert_eq!(seq.access(3), None);
    /// # Ok(())
    /// # }
    /// ```
    fn access(&self, mut pos: usize) -> Option<usize> {
        if self.len() <= pos {
            return None;
        }
        let mut x = 0;
        for j in 0..self.num_levels() {
            x |= usize::from(self.data[j][pos]) << (j * LEVEL_WIDTH);
            if j == self.num_levels() - 1
                || !bit_vectors::Access::access(&self.flags[j], pos).unwrap()
            {
                break;
            }
            pos = self.flags[j].rank1(pos).unwrap();
        }
        Some(x)
    }
}

/// Iterator for enumerating integers, created by [`DacsByte::iter()`].
pub struct Iter<'a> {
    seq: &'a DacsByte,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(seq: &'a DacsByte) -> Self {
        Self { seq, pos: 0 }
    }
}

impl Iterator for Iter<'_> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.seq.len() {
            let x = self.seq.access(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.seq.len(), Some(self.seq.len()))
    }
}

impl Serializable for DacsByte {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.data.serialize_into(&mut writer)?;
        mem += self.flags.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let data = Vec::<Vec<u8>>::deserialize_from(&mut reader)?;
        let flags = Vec::<Rank9Sel>::deserialize_from(&mut reader)?;
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
        let seq = DacsByte::from_slice(&[0xFFFFusize, 0xFF, 0xF, 0xFFFFF, 0xF]);

        assert_eq!(
            seq.data,
            vec![
                vec![0xFF, 0xFF, 0xF, 0xFF, 0xF],
                vec![0xFF, 0xFF],
                vec![0xF]
            ]
        );

        assert_eq!(
            seq.flags,
            vec![
                Rank9Sel::from_bits([true, false, false, true, false]),
                Rank9Sel::from_bits([false, true])
            ]
        );

        assert!(!seq.is_empty());
        assert_eq!(seq.len(), 5);
        assert_eq!(seq.num_levels(), 3);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH, LEVEL_WIDTH, LEVEL_WIDTH]);

        assert_eq!(seq.access(0), Some(0xFFFF));
        assert_eq!(seq.access(1), Some(0xFF));
        assert_eq!(seq.access(2), Some(0xF));
        assert_eq!(seq.access(3), Some(0xFFFFF));
        assert_eq!(seq.access(4), Some(0xF));
    }

    #[test]
    fn test_empty() {
        let seq = DacsByte::from_slice::<usize>(&[]);
        assert!(seq.is_empty());
        assert_eq!(seq.len(), 0);
        assert_eq!(seq.num_levels(), 1);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH]);
    }

    #[test]
    fn test_all_zeros() {
        let seq = DacsByte::from_slice(&[0usize, 0, 0, 0]);
        assert!(!seq.is_empty());
        assert_eq!(seq.len(), 4);
        assert_eq!(seq.num_levels(), 1);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH]);
        assert_eq!(seq.access(0), Some(0));
        assert_eq!(seq.access(1), Some(0));
        assert_eq!(seq.access(2), Some(0));
        assert_eq!(seq.access(3), Some(0));
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let seq = DacsByte::from_slice(&[0xFFFFFu32, 0xFF, 0xF, 0xFFFFF, 0xF]);
        let size = seq.serialize_into(&mut bytes).unwrap();
        let other = DacsByte::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(seq, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, seq.size_in_bytes());
    }
}
