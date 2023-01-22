//! Compressed integer list with Directly Addressable Codes (DACs).
#![cfg(target_pointer_width = "64")]

pub mod iter;

use std::io::{Read, Write};

use anyhow::{anyhow, Result};

use crate::util;
use crate::{BitVector, CompactVector, RsBitVector, Searial};
use iter::Iter;

/// Compressed integer list with Directly Addressable Codes (DACs).
///
/// This stores a list of integers in a compressed space with DACs of a fixed-width scheme.
/// When the list consists of small integers, the representation will be very compact.
///
/// # Examples
///
/// ## Specifying a fixed number of bits for each level
///
/// ```
/// use sucds::DacsList;
///
/// let list = DacsList::with_fixed_width(&[5, 0, 256, 255], 4).unwrap();
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
/// ## Computing an optimal assignment in space.
///
/// ```
/// use sucds::DacsList;
///
/// let list = DacsList::with_optimal_assignment(&[5, 0, 256, 255], None).unwrap();
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
pub struct DacsList {
    data: Vec<CompactVector>,
    flags: Vec<RsBitVector>,
}

impl DacsList {
    /// Builds DACs by assigning a fixed number of bits for each level.
    ///
    /// # Arguments
    ///
    /// - `ints`: Integers to be stored.
    /// - `width`: Number of bits for each level.
    pub fn with_fixed_width(ints: &[usize], width: usize) -> Result<Self> {
        if !(1..=64).contains(&width) {
            return Err(anyhow!("width must be in 1..=64, but got {width}"));
        }

        if ints.is_empty() {
            return Ok(Self::default());
        }

        let widths = Self::compute_fixed_widths(ints, width);
        Self::build(ints, &widths)
    }

    /// Builds DACs by assigning the optimal number of bits for each level.
    ///
    /// # Arguments
    ///
    /// - `ints`: Integers to be stored.
    /// - `max_levels`: Maximum number of levels defined.
    pub fn with_optimal_assignment(ints: &[usize], max_levels: Option<usize>) -> Result<Self> {
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

    fn compute_fixed_widths(ints: &[usize], width: usize) -> Vec<usize> {
        let num_bits = util::needed_bits(ints.iter().cloned().max().unwrap());
        let num_levels = util::ceiled_divide(num_bits, width);
        (0..num_levels).map(|_| width).collect()
    }

    fn compute_opt_widths(ints: &[usize], max_levels: usize) -> Vec<usize> {
        // Computes the number of bits needed to represent an integer at least.
        let num_bits = util::needed_bits(ints.iter().cloned().max().unwrap());

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
        //            provided that at most r+1 more levels are used.
        let mut dp_s = vec![vec![0; max_levels]; num_bits + 1];
        // dp_b[j,r]: Number of bits for the (r+1)-th level from the bottom to achieve dp_s[j,r].
        let mut dp_b = vec![vec![0; max_levels]; num_bits + 1];

        for j in 0..num_bits {
            dp_b[j][0] = num_bits - j;
            dp_s[j][0] = dp_b[j][0] * nums_ints[j];
        }

        for r in 1..max_levels {
            for j in 0..num_bits {
                dp_s[j][r] = usize::MAX;
                for b in 1..=num_bits - j {
                    let c = (b + 1) * nums_ints[j] + dp_s[j + b][r - 1];
                    if c < dp_s[j][r] {
                        dp_s[j][r] = c;
                        dp_b[j][r] = b;
                    }
                }
            }
        }

        let mut widths = vec![0; max_levels];
        let (mut j, mut r) = (0, 0);

        while j < num_bits {
            widths[r] = dp_b[j][max_levels - r - 1];
            j += widths[r];
            r += 1;
        }
        widths
    }

    fn build(ints: &[usize], widths: &[usize]) -> Result<Self> {
        assert!(!ints.is_empty());
        assert!(!widths.is_empty());

        if widths.len() == 1 {
            let mut data = CompactVector::with_len(ints.len(), widths[0]);
            for (i, &x) in ints.iter().enumerate() {
                data.set(i, x);
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
                data[j].push(x & mask);
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

    /// Gets the `pos`-th integer.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position to get.
    ///
    /// # Complexity
    ///
    /// - $`O( \lceil b_i / w \rceil )`$ where $`b_i`$ is the number of bits needed to represent
    ///   the `pos`-th integer and $`w`$ is [`Self::width()`].
    pub fn get(&self, mut pos: usize) -> usize {
        let mut x = 0;
        let mut width = 0;
        for j in 0..self.num_levels() {
            x |= self.data[j].get(pos) << (j * width);
            if j == self.num_levels() - 1 || !self.flags[j].get_bit(pos) {
                break;
            }
            pos = self.flags[j].rank1(pos);
            width = self.data[j].width();
        }
        x
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::DacsList;
    ///
    /// let list = DacsList::with_fixed_width(&[5, 0, 256, 255], 4).unwrap();
    /// let mut it = list.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(0));
    /// assert_eq!(it.next(), Some(256));
    /// assert_eq!(it.next(), Some(255));
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

impl Default for DacsList {
    fn default() -> Self {
        Self {
            data: vec![CompactVector::default()],
            flags: vec![],
        }
    }
}

impl Searial for DacsList {
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
    fn test_zero_width() {
        let list = DacsList::with_fixed_width(&[0, 1, 2, 3], 0);
        assert!(list.is_err());
    }

    #[test]
    fn test_empty() {
        let list = DacsList::with_fixed_width(&[], 1).unwrap();
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert_eq!(list.num_levels(), 1);
    }

    #[test]
    fn test_all_zeros() {
        let list = DacsList::with_fixed_width(&[0, 0, 0, 0], 1).unwrap();
        assert!(!list.is_empty());
        assert_eq!(list.len(), 4);
        assert_eq!(list.num_levels(), 1);
        assert_eq!(list.get(0), 0);
        assert_eq!(list.get(1), 0);
        assert_eq!(list.get(2), 0);
        assert_eq!(list.get(3), 0);
    }

    #[test]
    fn test_one_level() {
        let list = DacsList::with_fixed_width(&[4, 32, 0, 255], 8).unwrap();
        assert!(!list.is_empty());
        assert_eq!(list.len(), 4);
        assert_eq!(list.num_levels(), 1);
        assert_eq!(list.get(0), 4);
        assert_eq!(list.get(1), 32);
        assert_eq!(list.get(2), 0);
        assert_eq!(list.get(3), 255);
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let list = DacsList::with_fixed_width(&[4, 256, 0, 255], 4).unwrap();
        let size = list.serialize_into(&mut bytes).unwrap();
        let other = DacsList::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(list, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, list.size_in_bytes());
    }
}
