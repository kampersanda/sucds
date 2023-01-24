//! Compressed integer array using Directly Addressable Codes (DACs) with optimal assignment.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};

use anyhow::{anyhow, Result};

use crate::util;
use crate::{BitVector, CompactVector, IntGetter, RsBitVector, Searial};

/// Compressed integer array using Directly Addressable Codes (DACs) with optimal assignment.
///
/// DACs are a compact representation of an integer array consisting of many small values.
/// [`DacsOpt`] uses dynamic programming to compute the configuration
/// to achieve the minimum memory usage.
///
/// # Examples
///
/// ```
/// use sucds::{DacsOpt, IntGetter};
///
/// // Specifies two for the maximum number of levels to control time efficiency.
/// let list = DacsOpt::from_slice(&[5, 0, 100000, 334], Some(2)).unwrap();
///
/// assert_eq!(list.get_int(0), Some(5));
/// assert_eq!(list.get_int(1), Some(0));
/// assert_eq!(list.get_int(2), Some(100000));
/// assert_eq!(list.get_int(3), Some(334));
///
/// assert_eq!(list.len(), 4);
/// assert_eq!(list.num_levels(), 2);
/// ```
///
/// # References
///
/// - N. R. Brisaboa, S. Ladra, and G. Navarro, "DACs: Bringing direct access to variable-length
///   codes." Information Processing & Management, 49(1), 392-404, 2013.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DacsOpt {
    data: Vec<CompactVector>,
    flags: Vec<RsBitVector>,
}

impl DacsOpt {
    /// Builds DACs with the minimum memory usage by dynamic programming.
    ///
    /// # Arguments
    ///
    /// - `ints`: Integers to be stored.
    /// - `max_levels`: Maximum number of levels. The resulting number of levels is related to
    ///                 the access time. The smaller this value is, the faster operations can be,
    ///                 but the larger the memory can be. If [`None`], it computes configuration
    ///                 without limitation in the number of levels.
    ///
    /// # Complexities
    ///
    /// $`O(nw + w^3)`$ where $`n`$ is the number of integers, and $`w`$ is the word size in bits.
    pub fn from_slice(ints: &[usize], max_levels: Option<usize>) -> Result<Self> {
        let max_levels = max_levels.unwrap_or(64);
        if !(1..=64).contains(&max_levels) {
            return Err(anyhow!(
                "max_levels must be in 1..=64, but got {max_levels}"
            ));
        }

        if ints.is_empty() {
            return Ok(Self::default());
        }

        let widths = Self::compute_opt_widths(ints, max_levels);
        Self::build(ints, &widths)
    }

    // A modified implementation of Algorithm 3.5 in Navarro's book.
    fn compute_opt_widths(ints: &[usize], max_levels: usize) -> Vec<usize> {
        assert_ne!(max_levels, 0);

        // Computes the number of bits needed to represent an integer at least.
        let num_bits = util::needed_bits(ints.iter().cloned().max().unwrap());
        let max_levels = max_levels.min(num_bits);

        // Computes the number of integers with more than j bits.
        let nums_ints = {
            let mut nums_ints = vec![0; num_bits + 1];
            for &x in ints {
                nums_ints[util::needed_bits(x) - 1] += 1;
            }
            for j in (0..num_bits).rev() {
                nums_ints[j] += nums_ints[j + 1];
            }
            nums_ints
        };

        debug_assert_eq!(nums_ints[0], ints.len());
        debug_assert_eq!(*nums_ints.last().unwrap(), 0);

        // dp_s[j,r]: Possible smallest total space to encode integers with more than j bits,
        //            provided that r+1 further levels are used.
        let mut dp_s = vec![vec![0; max_levels]; num_bits + 1];
        // dp_b[j,r]: Number of bits for the (r+1)-th level from the bottom to achieve dp_s[j,r].
        let mut dp_b = vec![vec![0; max_levels]; num_bits + 1];

        for j in 0..num_bits {
            // NOTE(kampersabda): Here does not assume the space for flags,
            // i.e., +1 is omitted.
            dp_s[j][0] = (num_bits - j) * nums_ints[j];
            dp_b[j][0] = num_bits - j;
        }

        for r in 1..max_levels {
            for j in 0..num_bits {
                dp_s[j][r] = usize::MAX;
                for b in 1..=num_bits - j {
                    let c = (b + 1) * nums_ints[j] + dp_s[j + b][r - 1];
                    // NOTE(kampersabda): This comparison should use <=, not <,
                    // because a larger b allows to suppress the resulting height.
                    if c <= dp_s[j][r] {
                        dp_s[j][r] = c;
                        dp_b[j][r] = b;
                    }
                }
            }
        }

        // Search the number of levels to achieve the minimum space.
        let mut min_level_idx = 0;
        for r in 1..max_levels {
            if dp_s[0][r] < dp_s[0][min_level_idx] {
                min_level_idx = r;
            }
        }

        let num_levels = min_level_idx + 1;
        let mut widths = vec![0; num_levels];
        let (mut j, mut r) = (0, 0);

        while j < num_bits {
            widths[r] = dp_b[j][num_levels - r - 1];
            j += widths[r];
            r += 1;
        }

        assert_eq!(j, num_bits);
        assert_eq!(r, num_levels);
        assert_eq!(widths.iter().sum::<usize>(), num_bits);

        widths
    }

    fn build(ints: &[usize], widths: &[usize]) -> Result<Self> {
        assert!(!ints.is_empty());
        assert!(!widths.is_empty());

        if widths.len() == 1 {
            let mut data = CompactVector::with_len(ints.len(), widths[0]);
            for (i, &x) in ints.iter().enumerate() {
                data.set_int(i, x).unwrap();
            }
            return Ok(Self {
                data: vec![data],
                flags: vec![],
            });
        }

        let mut data: Vec<_> = widths.iter().map(|&w| CompactVector::new(w)).collect();
        let mut flags = vec![BitVector::default(); widths.len() - 1];

        for mut x in ints.iter().cloned() {
            for (j, &width) in widths.iter().enumerate() {
                let mask = (1 << width) - 1;
                data[j].push_int(x & mask);
                x >>= width;
                if j == widths.len() - 1 {
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
        Ok(Self { data, flags })
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::DacsOpt;
    ///
    /// let list = DacsOpt::from_slice(&[5, 0, 100000, 334], Some(2)).unwrap();
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
        self.data.iter().map(|d| d.width()).collect()
    }
}

impl Default for DacsOpt {
    fn default() -> Self {
        Self {
            data: vec![CompactVector::default()],
            flags: vec![],
        }
    }
}

impl IntGetter for DacsOpt {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// - $`O( \ell_{pos} )`$ where $`\ell_{pos}`$ is the number of levels corresponding to
    ///   the `pos`-th integer.
    fn get_int(&self, mut pos: usize) -> Option<usize> {
        let mut x = 0;
        let mut width = 0;
        for j in 0..self.num_levels() {
            x |= self.data[j].get_int(pos).unwrap() << (j * width);
            if j == self.num_levels() - 1 || !self.flags[j].get_bit(pos) {
                break;
            }
            pos = self.flags[j].rank1(pos);
            width = self.data[j].width();
        }
        Some(x)
    }
}

/// Iterator for enumerating integers, created by [`DacsOpt::iter()`].
pub struct Iter<'a> {
    list: &'a DacsOpt,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(list: &'a DacsOpt) -> Self {
        Self { list, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.list.len() {
            let x = self.list.get_int(self.pos).unwrap();
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

impl Searial for DacsOpt {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.data.serialize_into(&mut writer)?;
        mem += self.flags.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let data = Vec::<CompactVector>::deserialize_from(&mut reader)?;
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
    fn test_opt_witdhs_0() {
        let widths = DacsOpt::compute_opt_widths(&[0b0, 0b0, 0b0, 0b0], 3);
        assert_eq!(widths, vec![1]);
    }

    #[test]
    fn test_opt_witdhs_1() {
        let widths = DacsOpt::compute_opt_widths(&[0b11, 0b1, 0b1111, 0b11], 1);
        assert_eq!(widths, vec![4]);
    }

    #[test]
    fn test_opt_witdhs_2() {
        let widths = DacsOpt::compute_opt_widths(&[0b11, 0b1, 0b1111, 0b11], 2);
        assert_eq!(widths, vec![2, 2]);
    }

    #[test]
    fn test_opt_witdhs_3() {
        let widths = DacsOpt::compute_opt_widths(&[0b11, 0b1, 0b1111, 0b11], 3);
        assert_eq!(widths, vec![2, 2]);
    }

    #[test]
    fn test_opt_witdhs_4() {
        let widths = DacsOpt::compute_opt_widths(&[0b1111, 0b1111, 0b1111, 0b1111], 3);
        assert_eq!(widths, vec![4]);
    }

    #[test]
    fn test_basic() {
        let list = DacsOpt::from_slice(&[0b11, 0b1, 0b1111, 0b11], None).unwrap();

        assert_eq!(
            list.data,
            vec![
                CompactVector::from_slice(&[0b11, 0b1, 0b11, 0b11]),
                CompactVector::from_slice(&[0b11]),
            ]
        );

        assert_eq!(
            list.flags,
            vec![RsBitVector::from_bits([false, false, true, false])]
        );

        assert!(!list.is_empty());
        assert_eq!(list.len(), 4);
        assert_eq!(list.num_levels(), 2);
        assert_eq!(list.widths(), vec![2, 2]);

        assert_eq!(list.get_int(0), Some(0b11));
        assert_eq!(list.get_int(1), Some(0b1));
        assert_eq!(list.get_int(2), Some(0b1111));
        assert_eq!(list.get_int(3), Some(0b11));
    }

    #[test]
    fn test_empty() {
        let list = DacsOpt::from_slice(&[], None).unwrap();
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert_eq!(list.num_levels(), 1);
        assert_eq!(list.widths(), vec![0]);
    }

    #[test]
    fn test_all_zeros() {
        let list = DacsOpt::from_slice(&[0, 0, 0, 0], None).unwrap();
        assert!(!list.is_empty());
        assert_eq!(list.len(), 4);
        assert_eq!(list.num_levels(), 1);
        assert_eq!(list.widths(), vec![1]);
        assert_eq!(list.get_int(0), Some(0));
        assert_eq!(list.get_int(1), Some(0));
        assert_eq!(list.get_int(2), Some(0));
        assert_eq!(list.get_int(3), Some(0));
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let list = DacsOpt::from_slice(&[0b11, 0b1, 0b1111, 0b11], None).unwrap();
        let size = list.serialize_into(&mut bytes).unwrap();
        let other = DacsOpt::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(list, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, list.size_in_bytes());
    }
}
