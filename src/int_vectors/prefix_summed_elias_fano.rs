//! Compressed integer sequence with prefix-summed Elias-Fano encoding.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};

use anyhow::{anyhow, Result};
use num_traits::ToPrimitive;

use crate::int_vectors::IntGetter;
use crate::mii_sequences::{EliasFano, EliasFanoBuilder};
use crate::Serializable;

/// Compressed integer sequence with prefix-summed Elias-Fano encoding.
///
/// This stores a sequence of integers by converting it into an increasing sequence
/// in a prefix-summing manner and representing it through the Elias-Fano encoding.
///
/// # Memory complexity
///
/// $`n \lceil \lg \frac{N}{n} \rceil + 2n + o(n)`$ bits where
///
/// - $`n`$ is the number of stored integers, and
/// - $`N`$ is the sum of integers plus 1.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use sucds::int_vectors::{PrefixSummedEliasFano, IntGetter};
///
/// let seq = PrefixSummedEliasFano::from_slice(&[5, 14, 334, 10])?;
///
/// // Need IntGetter
/// assert_eq!(seq.get_int(0), Some(5));
/// assert_eq!(seq.get_int(1), Some(14));
/// assert_eq!(seq.get_int(2), Some(334));
/// assert_eq!(seq.get_int(3), Some(10));
///
/// assert_eq!(seq.len(), 4);
/// assert_eq!(seq.sum(), 363);
/// # Ok(())
/// # }
/// ```
///
/// # Credits
///
/// This is a yet another Rust port of [succinct::elias_fano_list](https://github.com/ot/succinct/blob/master/elias_fano_list.hpp).
///
/// # References
///
///  - P. Elias, "Efficient storage and retrieval by content and address of static files,"
///    Journal of the ACM, 1974.
///  - R. Fano, "On the number of bits required to implement an associative memory,"
///    Memorandum 61. Computer Structures Group, Project MAC, MIT, 1971.
///  - D. Okanohara, and K. Sadakane, "Practical Entropy-Compressed Rank/Select Dictionary,"
///    In ALENEX, 2007.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct PrefixSummedEliasFano {
    ef: EliasFano,
}

impl PrefixSummedEliasFano {
    /// Creates a new sequence from a slice of integers.
    ///
    /// # Arguments
    ///
    /// - `vals`: Slice of integers to be stored.
    ///
    /// # Errors
    ///
    /// An error is returned if
    ///
    /// - `vals` contains an integer that cannot be cast to [`usize`], or
    /// - `vals` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::int_vectors::PrefixSummedEliasFano;
    ///
    /// let seq = PrefixSummedEliasFano::from_slice(&[5, 14, 334, 10])?;
    ///
    /// assert_eq!(seq.len(), 4);
    /// assert_eq!(seq.sum(), 363);
    /// # Ok(())
    /// # }
    /// ```
    pub fn from_slice<T>(vals: &[T]) -> Result<Self>
    where
        T: ToPrimitive,
    {
        if vals.is_empty() {
            return Err(anyhow!("vals must not be empty."));
        }
        let mut universe = 0;
        for x in vals {
            universe += x
                .to_usize()
                .ok_or_else(|| anyhow!("vals must consist only of values castable into usize."))?;
        }
        let mut b = EliasFanoBuilder::new(universe + 1, vals.len())?;
        let mut cur = 0;
        for x in vals {
            cur += x.to_usize().unwrap();
            b.push(cur)?;
        }
        Ok(Self { ef: b.build() })
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::int_vectors::PrefixSummedEliasFano;
    ///
    /// let seq = PrefixSummedEliasFano::from_slice(&[5, 14, 334, 10])?;
    /// let mut it = seq.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(14));
    /// assert_eq!(it.next(), Some(334));
    /// assert_eq!(it.next(), Some(10));
    /// assert_eq!(it.next(), None);
    /// # Ok(())
    /// # }
    /// ```
    pub const fn iter(&self) -> Iter {
        Iter::new(self)
    }

    /// Gets the number of integers.
    pub fn len(&self) -> usize {
        self.ef.len()
    }

    /// Checks if the sequence is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the sum of integers.
    pub const fn sum(&self) -> usize {
        self.ef.universe() - 1
    }
}

impl IntGetter for PrefixSummedEliasFano {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// Constant
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::int_vectors::{PrefixSummedEliasFano, IntGetter};
    ///
    /// let seq = PrefixSummedEliasFano::from_slice(&[5, 14, 334])?;
    /// assert_eq!(seq.get_int(0), Some(5));
    /// assert_eq!(seq.get_int(1), Some(14));
    /// assert_eq!(seq.get_int(2), Some(334));
    /// assert_eq!(seq.get_int(3), None);
    /// # Ok(())
    /// # }
    /// ```
    fn get_int(&self, pos: usize) -> Option<usize> {
        self.ef.delta(pos)
    }
}

impl Serializable for PrefixSummedEliasFano {
    fn serialize_into<W: Write>(&self, writer: W) -> Result<usize> {
        self.ef.serialize_into(writer)
    }

    fn deserialize_from<R: Read>(reader: R) -> Result<Self> {
        let ef = EliasFano::deserialize_from(reader)?;
        Ok(Self { ef })
    }

    fn size_in_bytes(&self) -> usize {
        self.ef.size_in_bytes()
    }
}

/// Iterator for enumerating integers, created by [`PrefixSummedEliasFano::iter()`].
pub struct Iter<'a> {
    efl: &'a PrefixSummedEliasFano,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(efl: &'a PrefixSummedEliasFano) -> Self {
        Self { efl, pos: 0 }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.efl.len() {
            let x = self.efl.get_int(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.efl.len(), Some(self.efl.len()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_slice_uncastable() {
        let e = PrefixSummedEliasFano::from_slice(&[u128::MAX]);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("vals must consist only of values castable into usize.".to_string())
        );
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let seq = PrefixSummedEliasFano::from_slice(&[5, 14, 334, 10]).unwrap();
        let size = seq.serialize_into(&mut bytes).unwrap();
        let other = PrefixSummedEliasFano::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(seq, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, seq.size_in_bytes());
    }
}
