//! Compressed integer list with Directly Addressable Codes (DACs) in the bytewise scheme.
#![cfg(target_pointer_width = "64")]

use std::convert::TryInto;

use crate::util;
use crate::{BitVector, RsBitVector};

const LEVEL_WIDTH: usize = 8;
const LEVEL_MASK: usize = (1 << LEVEL_WIDTH) - 1;

/// Compressed integer list with Directly Addressable Codes (DACs) in the bytewise scheme.
///
/// # Examples
///
/// ```
/// use sucds::DacsByte;
///
/// let list = DacsByte::from_slice(&[5, 0, 256, 255]);
///
/// assert_eq!(list.get(0), 5);
/// assert_eq!(list.get(1), 0);
/// assert_eq!(list.get(2), 256);
/// assert_eq!(list.get(3), 255);
///
/// assert_eq!(list.len(), 4);
/// ```
///
/// # References
///
/// - N. R. Brisaboa, S. Ladra, and G. Navarro, "DACs: Bringing direct access to variable-length
///   codes." Information Processing & Management, 49(1), 392-404, 2013.
pub struct DacsByte {
    bytes: Vec<Vec<u8>>,
    flags: Vec<RsBitVector>,
}

impl DacsByte {
    /// Creates an instance from a slice of integers.
    ///
    /// # Arguments
    ///
    /// - `ints`: Integers to be stored.
    pub fn from_slice(ints: &[usize]) -> Self {
        if ints.is_empty() {
            return Self::default();
        }

        let maxv = ints.iter().cloned().max().unwrap();
        let bits = util::needed_bits(maxv);

        // .max(1) is required for the case of all zeros.
        let num_levels = util::ceiled_divide(bits, LEVEL_WIDTH).max(1);

        if num_levels == 1 {
            let bytes: Vec<_> = ints.iter().map(|&x| x.try_into().unwrap()).collect();
            return Self {
                bytes: vec![bytes],
                flags: vec![],
            };
        }

        let mut bytes = vec![];
        let mut flags = vec![];
        bytes.resize(num_levels, vec![]);
        flags.resize(num_levels - 1, BitVector::default());

        for mut x in ints.iter().cloned() {
            for j in 0..num_levels {
                bytes[j].push((x & LEVEL_MASK) as u8);
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

        let flags = flags.into_iter().map(|f| RsBitVector::new(f)).collect();
        Self { bytes, flags }
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
            x |= usize::from(self.bytes[j][pos]) << (j * LEVEL_WIDTH);
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
        self.bytes[0].len()
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of levels.
    #[inline(always)]
    pub fn num_levels(&self) -> usize {
        self.bytes.len()
    }
}

impl Default for DacsByte {
    fn default() -> Self {
        Self {
            bytes: vec![vec![]],
            flags: vec![],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let list = DacsByte::from_slice(&[]);
        assert_eq!(list.len(), 0);
        assert!(list.is_empty());
        assert_eq!(list.num_levels(), 1);
    }

    #[test]
    fn test_all_zeros() {
        let list = DacsByte::from_slice(&[0, 0, 0, 0]);
        assert_eq!(list.len(), 4);
        assert!(!list.is_empty());
        assert_eq!(list.num_levels(), 1);
        assert_eq!(list.get(0), 0);
        assert_eq!(list.get(1), 0);
        assert_eq!(list.get(2), 0);
        assert_eq!(list.get(3), 0);
    }

    #[test]
    fn test_one_level() {
        let list = DacsByte::from_slice(&[4, 255, 0, 13]);
        assert_eq!(list.len(), 4);
        assert!(!list.is_empty());
        assert_eq!(list.num_levels(), 1);
        assert_eq!(list.get(0), 4);
        assert_eq!(list.get(1), 255);
        assert_eq!(list.get(2), 0);
        assert_eq!(list.get(3), 13);
    }

    #[test]
    fn test_two_level() {
        let list = DacsByte::from_slice(&[4, 256, 0, 65535]);
        assert_eq!(list.len(), 4);
        assert!(!list.is_empty());
        assert_eq!(list.num_levels(), 2);
        assert_eq!(list.get(0), 4);
        assert_eq!(list.get(1), 256);
        assert_eq!(list.get(2), 0);
        assert_eq!(list.get(3), 65535);
    }

    #[test]
    fn test_four_level() {
        let list = DacsByte::from_slice(&[4, 16777216, 0, 4294967295]);
        assert_eq!(list.len(), 4);
        assert!(!list.is_empty());
        assert_eq!(list.num_levels(), 4);
        assert_eq!(list.get(0), 4);
        assert_eq!(list.get(1), 16777216);
        assert_eq!(list.get(2), 0);
        assert_eq!(list.get(3), 4294967295);
    }

    #[test]
    fn test_eight_level() {
        let list = DacsByte::from_slice(&[4, 4294967296, 0, 18446744073709551615]);
        assert_eq!(list.len(), 4);
        assert!(!list.is_empty());
        assert_eq!(list.num_levels(), 8);
        assert_eq!(list.get(0), 4);
        assert_eq!(list.get(1), 4294967296);
        assert_eq!(list.get(2), 0);
        assert_eq!(list.get(3), 18446744073709551615);
    }
}
