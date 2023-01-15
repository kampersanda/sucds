//! Compressed integer list with Directly Addressable Codes (DACs) in the bytewise scheme.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};

use anyhow::{anyhow, Result};

use crate::util;
use crate::{BitVector, CompactVector, RsBitVector, Searial};

/// Compressed integer list with Directly Addressable Codes (DACs) in the bytewise scheme.
///
/// # Examples
///
/// ```
/// use sucds::DacsByte;
///
/// let list = DacsByte::from_slice(&[5, 0, 256, 255], 4).unwrap();
///
/// assert_eq!(list.get(0), 5);
/// assert_eq!(list.get(1), 0);
/// assert_eq!(list.get(2), 256);
/// assert_eq!(list.get(3), 255);
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
    data: Vec<CompactVector>,
    flags: Vec<RsBitVector>,
    width: usize,
}

impl DacsByte {
    /// Creates an instance from a slice of integers.
    ///
    /// # Arguments
    ///
    /// - `ints`: Integers to be stored.
    /// - `width`: Number of bits for each level.
    pub fn from_slice(ints: &[usize], width: usize) -> Result<Self> {
        if !(1..=64).contains(&width) {
            return Err(anyhow!("width must be in 1..=64, but got {width}"));
        }

        if ints.is_empty() {
            return Ok(Self::default());
        }

        let maxv = ints.iter().cloned().max().unwrap();
        let bits = util::needed_bits(maxv);

        // .max(1) is required for the case of all zeros.
        let num_levels = util::ceiled_divide(bits, width).max(1);

        if num_levels == 1 {
            let mut data = CompactVector::with_len(ints.len(), width);
            for (i, &x) in ints.iter().enumerate() {
                data.set(i, x);
            }
            return Ok(Self {
                data: vec![data],
                flags: vec![],
                width,
            });
        }

        let mut data = vec![];
        let mut flags = vec![];
        data.resize(num_levels, CompactVector::new(width));
        flags.resize(num_levels - 1, BitVector::default());

        let mask = (1 << width) - 1;

        for mut x in ints.iter().cloned() {
            for j in 0..num_levels {
                data[j].push(x & mask);
                x >>= width;
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

        let flags = flags.into_iter().map(|f| RsBitVector::new(f)).collect();
        Ok(Self { data, flags, width })
    }

    /// Gets the `i`-th integer.
    ///
    /// # Arguments
    ///
    /// - `i`: Position to get.
    ///
    /// # Complexity
    ///
    /// - Constant
    pub fn get(&self, mut pos: usize) -> usize {
        let mut x = 0;
        for j in 0..self.num_levels() {
            x |= usize::from(self.data[j].get(pos)) << (j * self.width);
            if j == self.num_levels() - 1 || !self.flags[j].get_bit(pos) {
                break;
            }
            pos = self.flags[j].rank1(pos);
        }
        x
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
}

impl Default for DacsByte {
    fn default() -> Self {
        Self {
            data: vec![CompactVector::default()],
            flags: vec![],
            width: 0,
        }
    }
}

impl Searial for DacsByte {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.data.serialize_into(&mut writer)?;
        mem += self.flags.serialize_into(&mut writer)?;
        mem += self.width.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let data = Vec::<CompactVector>::deserialize_from(&mut reader)?;
        let flags = Vec::<RsBitVector>::deserialize_from(&mut reader)?;
        let width = usize::deserialize_from(&mut reader)?;
        Ok(Self { data, flags, width })
    }

    fn size_in_bytes(&self) -> usize {
        self.data.size_in_bytes() + self.flags.size_in_bytes() + usize::size_of().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let list = DacsByte::from_slice(&[], 1).unwrap();
        assert_eq!(list.len(), 0);
        assert!(list.is_empty());
        assert_eq!(list.num_levels(), 1);
    }

    #[test]
    fn test_all_zeros() {
        let list = DacsByte::from_slice(&[0, 0, 0, 0], 1).unwrap();
        assert_eq!(list.len(), 4);
        assert!(!list.is_empty());
        assert_eq!(list.num_levels(), 1);
        assert_eq!(list.get(0), 0);
        assert_eq!(list.get(1), 0);
        assert_eq!(list.get(2), 0);
        assert_eq!(list.get(3), 0);
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let list = DacsByte::from_slice(&[4, 256, 0, 255], 4).unwrap();
        let size = list.serialize_into(&mut bytes).unwrap();
        let other = DacsByte::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(list, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, list.size_in_bytes());
    }
}
