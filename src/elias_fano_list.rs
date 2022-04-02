#![cfg(target_pointer_width = "64")]

pub mod iter;

use std::io::{Read, Write};

use anyhow::Result;

use crate::elias_fano_list::iter::Iter;
use crate::{EliasFano, EliasFanoBuilder};

/// Compressed integer list with prefix-summed Elias-Fano encoding.
///
/// [`EliasFanoList`] stores a list of integers by converting it into an increasing sequence
/// in a prefix-summing manner and representing the sequence through Elias-Fano encoding.
/// When the list consists of small integers, the representation will be very compact.
///
/// This is a yet another Rust port of [succinct::elias_fano_list](https://github.com/ot/succinct/blob/master/elias_fano_list.hpp).
///
/// # Example
///
/// ```
/// use sucds::EliasFanoList;
///
/// let list = EliasFanoList::from_slice(&[5, 14, 2, 10]).unwrap();
///
/// assert_eq!(list.get(0), 5);
/// assert_eq!(list.get(1), 14);
/// assert_eq!(list.get(2), 2);
/// assert_eq!(list.get(3), 10);
///
/// assert_eq!(list.len(), 4);
/// assert_eq!(list.sum(), 31);
///
/// let mut bytes = vec![];
/// let size = list.serialize_into(&mut bytes).unwrap();
/// let other = EliasFanoList::deserialize_from(&bytes[..]).unwrap();
/// assert_eq!(list, other);
/// assert_eq!(size, bytes.len());
/// assert_eq!(size, list.size_in_bytes());
/// ```
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct EliasFanoList {
    ef: EliasFano,
}

impl EliasFanoList {
    /// Creates a new [`EliasFanoList`] from a slice of integers.
    ///
    /// # Arguments
    ///
    /// - `ints`: Integers to be stored.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::EliasFanoList;
    ///
    /// let list = EliasFanoList::from_slice(&[5, 14, 2, 10]).unwrap();
    ///
    /// assert_eq!(list.len(), 4);
    /// assert_eq!(list.sum(), 31);
    /// ```
    pub fn from_slice(ints: &[usize]) -> Result<Self> {
        let mut universe = 0;
        for &x in ints {
            universe += x;
        }
        let mut b = EliasFanoBuilder::new(universe + 1, ints.len())?;
        let mut cur = 0;
        for &x in ints {
            cur += x;
            b.push(cur)?;
        }
        Ok(Self { ef: b.build() })
    }

    /// Serializes the data structure into the writer,
    /// returning the number of serialized bytes.
    ///
    /// # Arguments
    ///
    /// - `writer`: `std::io::Write` variable.
    pub fn serialize_into<W: Write>(&self, writer: W) -> Result<usize> {
        self.ef.serialize_into(writer)
    }

    /// Deserializes the data structure from the reader.
    ///
    /// # Arguments
    ///
    /// - `reader`: `std::io::Read` variable.
    pub fn deserialize_from<R: Read>(reader: R) -> Result<Self> {
        let ef = EliasFano::deserialize_from(reader)?;
        Ok(Self { ef })
    }

    /// Returns the number of bytes to serialize the data structure.
    pub fn size_in_bytes(&self) -> usize {
        self.ef.size_in_bytes()
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
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::EliasFanoList;
    ///
    /// let list = EliasFanoList::from_slice(&[5, 14, 2, 10]).unwrap();
    /// assert_eq!(list.get(0), 5);
    /// assert_eq!(list.get(1), 14);
    /// assert_eq!(list.get(2), 2);
    /// assert_eq!(list.get(3), 10);
    /// ```
    pub fn get(&self, i: usize) -> usize {
        self.ef.delta(i)
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::EliasFanoList;
    ///
    /// let list = EliasFanoList::from_slice(&[5, 14, 2, 10]).unwrap();
    /// let mut it = list.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(14));
    /// assert_eq!(it.next(), Some(2));
    /// assert_eq!(it.next(), Some(10));
    /// assert_eq!(it.next(), None);
    /// ```
    pub fn iter(&self) -> Iter {
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

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn gen_random_ints(len: usize, seed: u64) -> Vec<usize> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen_range(0..10000)).collect()
    }

    fn test_basic(ints: &[usize], list: &EliasFanoList) {
        let mut acc = 0;
        for (i, &x) in ints.iter().enumerate() {
            assert_eq!(x, list.get(i));
            acc += x;
        }
        assert_eq!(ints.len(), list.len());
        assert_eq!(acc, list.sum());
        for (i, x) in list.iter().enumerate() {
            assert_eq!(ints[i], x);
        }
    }

    #[test]
    fn test_random_ints() {
        for seed in 0..100 {
            let ints = gen_random_ints(10000, seed);
            let list = EliasFanoList::from_slice(&ints).unwrap();
            test_basic(&ints, &list);
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
