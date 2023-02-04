//! Compressed integer list with prefix-summed Elias-Fano encoding.
#![cfg(target_pointer_width = "64")]

pub mod iter;

use std::io::{Read, Write};

use anyhow::{anyhow, Result};
use num_traits::ToPrimitive;

use crate::elias_fano_list::iter::Iter;
use crate::{EliasFano, EliasFanoBuilder, IntGetter, Searial};

/// Compressed integer list with prefix-summed Elias-Fano encoding.
///
/// This stores a list of integers by converting it into an increasing sequence
/// in a prefix-summing manner and representing the sequence through Elias-Fano encoding.
/// When the list consists of small integers, the representation will be very compact.
///
/// This is a yet another Rust port of [succinct::elias_fano_list](https://github.com/ot/succinct/blob/master/elias_fano_list.hpp).
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use sucds::{EliasFanoList, IntGetter};
///
/// let list = EliasFanoList::from_slice(&[5, 14, 334, 10])?;
///
/// // Need IntGetter
/// assert_eq!(list.get_int(0), Some(5));
/// assert_eq!(list.get_int(1), Some(14));
/// assert_eq!(list.get_int(2), Some(334));
/// assert_eq!(list.get_int(3), Some(10));
///
/// assert_eq!(list.len(), 4);
/// assert_eq!(list.sum(), 363);
/// # Ok(())
/// # }
/// ```
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
pub struct EliasFanoList {
    ef: EliasFano,
}

impl EliasFanoList {
    /// Creates a new list from a slice of integers.
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
    /// use sucds::EliasFanoList;
    ///
    /// let list = EliasFanoList::from_slice(&[5, 14, 334, 10])?;
    ///
    /// assert_eq!(list.len(), 4);
    /// assert_eq!(list.sum(), 363);
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
            universe += x.to_usize().ok_or(anyhow!(
                "vals must consist only of values castable into usize."
            ))?;
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
    /// use sucds::EliasFanoList;
    ///
    /// let list = EliasFanoList::from_slice(&[5, 14, 334, 10])?;
    /// let mut it = list.iter();
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
    pub const fn len(&self) -> usize {
        self.ef.len()
    }

    /// Checks if the list is empty.
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the sum of integers.
    pub const fn sum(&self) -> usize {
        self.ef.universe() - 1
    }
}

impl IntGetter for EliasFanoList {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::{EliasFanoList, IntGetter};
    ///
    /// let list = EliasFanoList::from_slice(&[5, 14, 334])?;
    /// assert_eq!(list.get_int(0), Some(5));
    /// assert_eq!(list.get_int(1), Some(14));
    /// assert_eq!(list.get_int(2), Some(334));
    /// assert_eq!(list.get_int(3), None);
    /// # Ok(())
    /// # }
    /// ```
    fn get_int(&self, pos: usize) -> Option<usize> {
        self.ef.delta(pos)
    }
}

impl Searial for EliasFanoList {
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

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn gen_random_ints(len: usize, seed: u64) -> Vec<usize> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen_range(0..10000)).collect()
    }

    fn test_basic(vals: &[usize], list: &EliasFanoList) {
        let mut acc = 0;
        for (i, &x) in vals.iter().enumerate() {
            assert_eq!(list.get_int(i), Some(x));
            acc += x;
        }
        assert_eq!(vals.len(), list.len());
        assert_eq!(acc, list.sum());
        for (i, x) in list.iter().enumerate() {
            assert_eq!(vals[i], x);
        }
    }

    #[test]
    fn test_random_ints() {
        for seed in 0..100 {
            let vals = gen_random_ints(10000, seed);
            let list = EliasFanoList::from_slice(&vals).unwrap();
            test_basic(&vals, &list);
        }
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let list = EliasFanoList::from_slice(&gen_random_ints(10000, 42)).unwrap();
        let size = list.serialize_into(&mut bytes).unwrap();
        let other = EliasFanoList::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(list, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, list.size_in_bytes());
    }
}
