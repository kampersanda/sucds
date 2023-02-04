//! Compressed monotone increasing sequence through Elias-Fano encoding.
#![cfg(target_pointer_width = "64")]

pub mod iter;

use std::io::{Read, Write};
use std::ops::Range;

use anyhow::{anyhow, Result};

use crate::elias_fano::iter::Iter;
use crate::{broadword, darray::DArrayIndex, BitGetter, BitVector, Ranker, Searial, Selector};

const LINEAR_SCAN_THRESHOLD: usize = 64;

/// Compressed monotone increasing sequence through Elias-Fano encoding.
///
/// This implements an Elias-Fano representation for monotone increasing sequences.
/// When a sequence stores $`n`$ integers from $`[0, u-1]`$,
/// this representation takes $`n \lceil \log_2 \frac{u}{n} \rceil + 2n + o(n)`$ bits of space.
/// That is, a sparse sequence can be stored in a very compressed space.
///
/// This is a yet another Rust port of [succinct::elias_fano](https://github.com/ot/succinct/blob/master/elias_fano.hpp).
/// The implementation of binary search is based on that in
/// [tongrams::fast_ef_sequence](https://github.com/jermp/tongrams/blob/master/include/sequences/fast_ef_sequence.hpp).
///
/// # Example
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use sucds::{EliasFanoBuilder, Ranker, Selector};
///
/// let mut efb = EliasFanoBuilder::new(8, 4)?;
/// efb.append([1, 3, 3, 7])?;
/// let ef = efb.build();
///
/// assert_eq!(ef.len(), 4);
/// assert_eq!(ef.universe(), 8);
///
/// // Need Selector
/// assert_eq!(ef.select1(0), Some(1));
/// assert_eq!(ef.select1(1), Some(3));
/// assert_eq!(ef.select1(2), Some(3));
/// assert_eq!(ef.select1(3), Some(7));
///
/// // Builds an index to enable rank, predecessor, and successor.
/// let ef = ef.enable_rank();
///
/// // Need Ranker
/// assert_eq!(ef.rank1(3), Some(1));
/// assert_eq!(ef.rank1(4), Some(3));
///
/// assert_eq!(ef.predecessor(4), Some(3));
/// assert_eq!(ef.predecessor(3), Some(3));
/// assert_eq!(ef.successor(3), Some(3));
/// assert_eq!(ef.successor(4), Some(7));
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
pub struct EliasFano {
    high_bits: BitVector,
    high_bits_d1: DArrayIndex,
    high_bits_d0: Option<DArrayIndex>,
    low_bits: BitVector,
    low_len: usize,
    universe: usize,
}

impl EliasFano {
    /// Creates a new sequence from a bit stream.
    ///
    /// # Arguments
    ///
    /// - `bits`: Bit stream.
    ///
    /// # Errors
    ///
    /// An error is returned if `bits` contains no set bit.
    pub fn from_bits<I>(bits: I) -> Result<Self>
    where
        I: IntoIterator<Item = bool>,
    {
        let bv = BitVector::from_bits(bits);
        let n = bv.len();
        let m = (0..bv.num_words()).fold(0, |acc, i| acc + broadword::popcount(bv.words()[i]));
        let mut b = EliasFanoBuilder::new(n, m)?;
        for i in 0..n {
            if bv.get_bit(i).unwrap() {
                b.push(i)?;
            }
        }
        Ok(b.build())
    }

    /// Builds an index to enable operations [`EliasFano::rank1()`],
    /// [`EliasFano::predecessor()`], and [`EliasFano::successor()`].
    #[must_use]
    pub fn enable_rank(mut self) -> Self {
        self.high_bits_d0 = Some(DArrayIndex::new(&self.high_bits, false));
        self
    }

    /// Gets the largest integer `pred` such that `pred <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Predecessor query.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \frac{u}{n})`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.append([1, 3, 3, 7])?;
    /// let ef = efb.build().enable_rank();
    ///
    /// assert_eq!(ef.predecessor(4), Some(3));
    /// assert_eq!(ef.predecessor(3), Some(3));
    /// assert_eq!(ef.predecessor(2), Some(1));
    /// assert_eq!(ef.predecessor(0), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn predecessor(&self, pos: usize) -> Option<usize> {
        Some(self.rank1(pos + 1).unwrap())
            .filter(|&i| i > 0)
            .map(|i| self.select1(i - 1).unwrap())
    }

    /// Gets the smallest integer `succ` such that `succ >= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Successor query.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \frac{u}{n})`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.append([1, 3, 3, 7])?;
    /// let ef = efb.build().enable_rank();
    ///
    /// assert_eq!(ef.successor(0), Some(1));
    /// assert_eq!(ef.successor(2), Some(3));
    /// assert_eq!(ef.successor(3), Some(3));
    /// assert_eq!(ef.successor(8), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn successor(&self, pos: usize) -> Option<usize> {
        Some(self.rank1(pos).unwrap())
            .filter(|&i| i < self.len())
            .map(|i| self.select1(i).unwrap())
    }

    /// Gets the difference between the `k-1`-th and `k`-th integers
    /// (i.e., `select(k) - select(k-1)`), returning [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.append([1, 3, 3, 7])?;
    /// let ef = efb.build();
    ///
    /// assert_eq!(ef.delta(0), Some(1));
    /// assert_eq!(ef.delta(1), Some(2));
    /// assert_eq!(ef.delta(2), Some(0));
    /// assert_eq!(ef.delta(3), Some(4));
    /// assert_eq!(ef.delta(4), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn delta(&self, k: usize) -> Option<usize> {
        if self.len() <= k {
            return None;
        }
        let high_val = self.high_bits_d1.select(&self.high_bits, k).unwrap();
        let low_val = self
            .low_bits
            .get_bits(k * self.low_len, self.low_len)
            .unwrap();
        let x = if k != 0 {
            ((high_val - self.high_bits.predecessor1(high_val - 1).unwrap() - 1) << self.low_len)
                + low_val
                - self
                    .low_bits
                    .get_bits((k - 1) * self.low_len, self.low_len)
                    .unwrap()
        } else {
            ((high_val - k) << self.low_len) | low_val
        };
        Some(x)
    }

    /// Finds the position `k` such that `select(k) == val`.
    ///
    /// Note that, if there are multiple values of `val`, one of them is returned.
    ///
    /// # Arguments
    ///
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// - Logarithmic
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(11, 6)?;
    /// efb.append([1, 3, 3, 6, 7, 10])?;
    /// let ef = efb.build();
    ///
    /// assert_eq!(ef.find(6), Some(3));
    /// assert_eq!(ef.find(10), Some(5));
    /// assert_eq!(ef.find(9), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn find(&self, val: usize) -> Option<usize> {
        self.find_range(0..self.len(), val)
    }

    /// Finds the position `k` such that `select(k) == val` and `k in range`.
    ///
    /// Note that, if there are multiple values of `val`, one of them is returned.
    ///
    /// # Arguments
    ///
    /// - `range`: Position range to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// - Logarithmic for the range
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(11, 6)?;
    /// efb.append([1, 3, 3, 6, 7, 10])?;
    /// let ef = efb.build();
    ///
    /// assert_eq!(ef.find_range(1..4, 6), Some(3));
    /// assert_eq!(ef.find_range(5..6, 10), Some(5));
    /// assert_eq!(ef.find_range(1..3, 6), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn find_range(&self, range: Range<usize>, val: usize) -> Option<usize> {
        if range.is_empty() {
            return None;
        }

        // Binary search
        let (mut lo, mut hi) = (range.start, range.end);
        while hi - lo > LINEAR_SCAN_THRESHOLD {
            let mi = (lo + hi) / 2;
            let x = self.select1(mi).unwrap();
            if val == x {
                return Some(mi);
            }
            if val < x {
                hi = mi;
            } else {
                lo = mi + 1;
            }
        }

        // Linear scan
        let mut it = self.iter(lo);
        for i in lo..hi {
            let x = it.next().unwrap();
            if val == x {
                return Some(i);
            }
        }
        None
    }

    /// Creates an iterator of [`Iter`] to enumerate integers from the `k`-th one.
    ///
    /// # Arguments
    ///
    /// - `k`: Select query.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.append([1, 3, 3, 7])?;
    /// let ef = efb.build();
    ///
    /// let mut it = ef.iter(1);
    /// assert_eq!(it.next(), Some(3));
    /// assert_eq!(it.next(), Some(3));
    /// assert_eq!(it.next(), Some(7));
    /// assert_eq!(it.next(), None);
    /// # Ok(())
    /// # }
    /// ```
    pub fn iter(&self, k: usize) -> Iter {
        Iter::new(self, k)
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.high_bits_d1.len()
    }

    /// Checks if the sequence is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the universe, i.e., the (exclusive) upper bound of possible integers.
    #[inline(always)]
    pub const fn universe(&self) -> usize {
        self.universe
    }
}

impl Ranker for EliasFano {
    /// Returns the number of integers less than `pos` (and never [`None`]).
    ///
    /// # Complexity
    ///
    /// - $`O(\log \frac{u}{n})`$
    ///
    /// # Panics
    ///
    /// It panics if the index is not built by [`Self::enable_rank()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::{EliasFanoBuilder, Ranker};
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.append([1, 3, 3, 7])?;
    /// let ef = efb.build().enable_rank();
    ///
    /// assert_eq!(ef.rank1(1), Some(0));
    /// assert_eq!(ef.rank1(2), Some(1));
    /// assert_eq!(ef.rank1(3), Some(1));
    /// assert_eq!(ef.rank1(4), Some(3));
    /// # Ok(())
    /// # }
    /// ```
    fn rank1(&self, pos: usize) -> Option<usize> {
        let high_bits_d0 = self.high_bits_d0.as_ref().unwrap();

        if pos > self.universe() {
            return Some(self.len());
        }

        let h_rank = pos >> self.low_len;
        let mut h_pos = high_bits_d0.select(&self.high_bits, h_rank).unwrap();
        let mut rank = h_pos - h_rank;
        let l_pos = pos & ((1 << self.low_len) - 1);

        while h_pos > 0
            && self.high_bits.get_bit(h_pos - 1).unwrap()
            && self
                .low_bits
                .get_bits((rank - 1) * self.low_len, self.low_len)
                .unwrap()
                >= l_pos
        {
            rank -= 1;
            h_pos -= 1;
        }

        Some(rank)
    }

    /// Panics always because this operation is not supported.
    fn rank0(&self, _i: usize) -> Option<usize> {
        panic!("This operation is not supported.");
    }
}

impl Selector for EliasFano {
    /// Returns the position of the `k`-th smallest integer.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::{EliasFanoBuilder, Selector};
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.append([1, 3, 3, 7])?;
    /// let ef = efb.build();
    ///
    /// assert_eq!(ef.select1(0), Some(1));
    /// assert_eq!(ef.select1(1), Some(3));
    /// assert_eq!(ef.select1(2), Some(3));
    /// assert_eq!(ef.select1(3), Some(7));
    /// assert_eq!(ef.select1(4), None);
    /// # Ok(())
    /// # }
    /// ```
    fn select1(&self, k: usize) -> Option<usize> {
        if self.len() <= k {
            None
        } else {
            Some(
                ((self.high_bits_d1.select(&self.high_bits, k).unwrap() - k) << self.low_len)
                    | self
                        .low_bits
                        .get_bits(k * self.low_len, self.low_len)
                        .unwrap(),
            )
        }
    }

    /// Panics always because this operation is not supported.
    fn select0(&self, _k: usize) -> Option<usize> {
        panic!("This operation is not supported.");
    }
}

impl Searial for EliasFano {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = self.high_bits.serialize_into(&mut writer)?;
        mem += self.high_bits_d1.serialize_into(&mut writer)?;
        mem += self.high_bits_d0.serialize_into(&mut writer)?;
        mem += self.low_bits.serialize_into(&mut writer)?;
        mem += self.low_len.serialize_into(&mut writer)?;
        mem += self.universe.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let high_bits = BitVector::deserialize_from(&mut reader)?;
        let high_bits_d1 = DArrayIndex::deserialize_from(&mut reader)?;
        let high_bits_d0 = Option::<DArrayIndex>::deserialize_from(&mut reader)?;
        let low_bits = BitVector::deserialize_from(&mut reader)?;
        let low_len = usize::deserialize_from(&mut reader)?;
        let universe = usize::deserialize_from(&mut reader)?;
        Ok(Self {
            high_bits,
            high_bits_d1,
            high_bits_d0,
            low_bits,
            low_len,
            universe,
        })
    }

    fn size_in_bytes(&self) -> usize {
        self.high_bits.size_in_bytes()
            + self.high_bits_d1.size_in_bytes()
            + self.high_bits_d0.size_in_bytes()
            + self.low_bits.size_in_bytes()
            + usize::size_of().unwrap() * 2
    }
}

/// Builder for [`EliasFano`].
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use sucds::EliasFanoBuilder;
///
/// let mut efb = EliasFanoBuilder::new(8, 5)?;
///
/// assert_eq!(efb.universe(), 8);
/// assert_eq!(efb.num_vals(), 5);
///
/// efb.push(1)?;
/// efb.push(3)?;
/// efb.append([3, 5, 7])?;
///
/// let ef = efb.build();
/// assert_eq!(ef.len(), 5);
/// assert_eq!(ef.universe(), 8);
/// # Ok(())
/// # }
/// ```
pub struct EliasFanoBuilder {
    high_bits: BitVector,
    low_bits: BitVector,
    universe: usize,
    num_vals: usize,
    pos: usize,
    last: usize,
    low_len: usize,
}

impl EliasFanoBuilder {
    /// Creates a new builder.
    ///
    /// # Arguments
    ///
    /// - `universe`: The (exclusive) upper bound of integers to be stored, i.e., an integer in `[0..universe - 1]`.
    /// - `num_vals`: The number of integers that will be pushed (> 0).
    ///
    /// # Errors
    ///
    /// An error is returned if `num_vals == 0`.
    pub fn new(universe: usize, num_vals: usize) -> Result<Self> {
        if num_vals == 0 {
            return Err(anyhow!("num_vals must not be zero."));
        }
        let low_len = broadword::msb(universe / num_vals).unwrap_or(0);
        Ok(Self {
            high_bits: BitVector::from_bit(false, (num_vals + 1) + (universe >> low_len) + 1),
            low_bits: BitVector::new(),
            universe,
            num_vals,
            pos: 0,
            last: 0,
            low_len,
        })
    }

    /// Pushes integer `val` at the end.
    ///
    /// # Arguments
    ///
    /// - `val`: Pushed integer that must be no less than the last one.
    ///
    /// # Errors
    ///
    /// An error is returned if
    ///
    /// - `val` is less than the last one,
    /// - `val` is no less than [`Self::universe()`], or
    /// - the number of stored integers becomes no less than [`Self::num_vals()`].
    pub fn push(&mut self, val: usize) -> Result<()> {
        if val < self.last {
            return Err(anyhow!(
                "The input integer {} must be no less than the last one {}",
                val,
                self.last
            ));
        }
        if self.universe <= val {
            return Err(anyhow!(
                "The input integer {} must be less than the universe {}",
                val,
                self.universe
            ));
        }
        if self.num_vals <= self.pos {
            return Err(anyhow!(
                "The number of stored integers exceeds the given upper bound {}",
                self.num_vals
            ));
        }

        self.last = val;
        let low_mask = (1 << self.low_len) - 1;
        if self.low_len != 0 {
            self.low_bits
                .push_bits(val & low_mask, self.low_len)
                .unwrap();
        }
        self.high_bits
            .set_bit((val >> self.low_len) + self.pos, true)
            .unwrap();
        self.pos += 1;

        Ok(())
    }

    /// Appends integers at the end.
    ///
    /// # Arguments
    ///
    /// - `vals`: Pushed integers that are monotone increasing.
    ///
    /// # Errors
    ///
    /// An error is returned if
    ///
    /// - `vals` is not monotone increasing (also compared to the current last value),
    /// - values in `vals` is no less than [`Self::universe()`], or
    /// - the number of stored integers becomes no less than [`Self::num_vals()`].
    pub fn append<'a, I>(&mut self, vals: I) -> Result<()>
    where
        I: IntoIterator<Item = usize>,
    {
        for x in vals {
            self.push(x)?;
        }
        Ok(())
    }

    /// Builds [`EliasFano`] from the pushed integers.
    pub fn build(self) -> EliasFano {
        EliasFano {
            high_bits_d1: DArrayIndex::new(&self.high_bits, true),
            high_bits: self.high_bits,
            high_bits_d0: None,
            low_bits: self.low_bits,
            low_len: self.low_len,
            universe: self.universe,
        }
    }

    /// Returns the universe, i.e., the (exclusive) upper bound of possible integers.
    #[inline(always)]
    pub fn universe(&self) -> usize {
        self.universe
    }

    /// Returns the number of integers that can be stored.
    #[inline(always)]
    pub const fn num_vals(&self) -> usize {
        self.num_vals
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn gen_random_bits(len: usize, p: f64, seed: u64) -> Vec<bool> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen_bool(p)).collect()
    }

    fn gen_random_queries(bits: &[bool], len: usize, seed: u64) -> Vec<(usize, Option<usize>)> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        let mut queries = vec![];
        for _ in 0..len {
            let v = rng.gen_range(0..bits.len());
            queries.push(if bits[v] {
                let rank = bits[..v].iter().fold(0, |acc, &b| acc + b as usize);
                (v, Some(rank))
            } else {
                (v, None)
            })
        }
        queries
    }

    fn gen_random_range_queries(
        bits: &[bool],
        len: usize,
        seed: u64,
    ) -> Vec<(usize, Range<usize>, Option<usize>)> {
        let ints: Vec<usize> = bits
            .iter()
            .enumerate()
            .filter(|(_, &b)| b)
            .map(|(i, _)| i)
            .collect();
        let mut rng = ChaChaRng::seed_from_u64(seed);
        let mut queries = vec![];
        for _ in 0..len {
            let v = rng.gen_range(0..bits.len());
            let i = rng.gen_range(0..ints.len());
            let j = rng.gen_range(i..ints.len());
            queries.push(if let Some(p) = ints[i..j].iter().position(|&x| x == v) {
                (v, i..j, Some(p + i))
            } else {
                (v, i..j, None)
            })
        }
        queries
    }

    fn test_rank_select(bits: &[bool], ef: &EliasFano) {
        let mut cur_rank = 0;
        for i in 0..bits.len() {
            assert_eq!(ef.rank1(i), Some(cur_rank));
            if bits[i] {
                assert_eq!(ef.select1(cur_rank), Some(i));
                cur_rank += 1;
            }
        }
        assert_eq!(cur_rank, ef.len());
        assert_eq!(bits.len(), ef.universe());
    }

    fn test_successor_predecessor(bits: &[bool], ef: &EliasFano) {
        let one_positions: Vec<usize> = (0..bits.len()).filter(|&i| bits[i]).collect();

        let mut pos = 0;
        for &i in &one_positions {
            let next = ef.successor(pos).unwrap();
            debug_assert_eq!(i, next);
            pos = next + 1;
        }
        debug_assert!(pos == ef.universe() || ef.successor(pos).is_none());

        let mut pos = bits.len() - 1;
        for &i in one_positions.iter().rev() {
            let pred = ef.predecessor(pos).unwrap();
            debug_assert_eq!(i, pred);
            if pred == 0 {
                pos = ef.universe();
                break;
            }
            pos = pred - 1;
        }
        debug_assert!(pos == ef.universe() || ef.predecessor(pos).is_none());
    }

    fn test_find(ef: &EliasFano, queries: &[(usize, Option<usize>)]) {
        for &(val, expected) in queries {
            assert_eq!(ef.find(val), expected);
        }
    }

    fn test_find_range(ef: &EliasFano, queries: &[(usize, Range<usize>, Option<usize>)]) {
        for (val, rng, expected) in queries.iter().cloned() {
            assert_eq!(ef.find_range(rng, val), expected);
        }
    }

    #[test]
    fn test_random_bits_dense() {
        for seed in 0..100 {
            let bits = gen_random_bits(10000, 0.5, seed);
            let ef = EliasFano::from_bits(bits.iter().cloned())
                .unwrap()
                .enable_rank();
            test_rank_select(&bits, &ef);
            test_successor_predecessor(&bits, &ef);
            let queries = gen_random_queries(&bits, 100, seed + 100);
            test_find(&ef, &queries);
            let queries = gen_random_range_queries(&bits, 100, seed + 200);
            test_find_range(&ef, &queries);
        }
    }

    #[test]
    fn test_random_bits_sparse() {
        for seed in 0..100 {
            let bits = gen_random_bits(10000, 0.01, seed);
            let ef = EliasFano::from_bits(bits.iter().cloned())
                .unwrap()
                .enable_rank();
            test_rank_select(&bits, &ef);
            test_successor_predecessor(&bits, &ef);
            let queries = gen_random_queries(&bits, 100, seed + 100);
            test_find(&ef, &queries);
            let queries = gen_random_range_queries(&bits, 100, seed + 200);
            test_find_range(&ef, &queries);
        }
    }

    #[test]
    fn test_serialize_dense() {
        let mut bytes = vec![];
        let ef = EliasFano::from_bits(gen_random_bits(10000, 0.5, 42))
            .unwrap()
            .enable_rank();
        let size = ef.serialize_into(&mut bytes).unwrap();
        let other = EliasFano::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(ef, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, ef.size_in_bytes());
    }

    #[test]
    fn test_serialize_sparse() {
        let mut bytes = vec![];
        let ef = EliasFano::from_bits(gen_random_bits(10000, 0.01, 42))
            .unwrap()
            .enable_rank();
        let size = ef.serialize_into(&mut bytes).unwrap();
        let other = EliasFano::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(ef, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, ef.size_in_bytes());
    }

    #[test]
    #[should_panic]
    fn test_empty_ints() {
        EliasFanoBuilder::new(10, 0).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_exclusive_universe() {
        let mut b = EliasFanoBuilder::new(10, 4).unwrap();
        b.push(10).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_exclusive_ints() {
        let mut b = EliasFanoBuilder::new(10, 4).unwrap();
        b.append([1, 2, 3, 4, 5]).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_non_increasing() {
        let mut b = EliasFanoBuilder::new(10, 4).unwrap();
        b.append([1, 2, 3, 2]).unwrap();
    }
}
