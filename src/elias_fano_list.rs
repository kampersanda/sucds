#![cfg(target_pointer_width = "64")]

use crate::{EliasFano, EliasFanoBuilder};

use anyhow::Result;
use serde::{Deserialize, Serialize};

/// Compressed integer list based on through Elias-Fano gap encoding.
///
/// [`EliasFanoList`] stores a list of integers by converting it into an increasing sequence
/// in a prefix-summing manner and representing the sequence through Elias-Fano encoding.
/// When the list consists of small integers, the representation will very compact.
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
/// ```
#[derive(Serialize, Deserialize)]
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
        Ok(Self {
            ef: EliasFano::new(b, false),
        })
    }

    /// Gets the `i`-th integer.
    ///
    /// # Arguments
    ///
    /// - `i`: Position to get.
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

    /// Gets the number of integers.
    pub fn len(&self) -> usize {
        self.ef.len()
    }

    /// Gets the sum of integers.
    pub fn sum(&self) -> usize {
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
    }

    #[test]
    fn test_random_ints() {
        for seed in 0..100 {
            let ints = gen_random_ints(10000, seed);
            let list = EliasFanoList::from_slice(&ints).unwrap();
            test_basic(&ints, &list);
        }
    }
}
