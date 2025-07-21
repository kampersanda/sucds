//! Compressed monotone increasing sequence through Elias-Fano encoding.
#![cfg(target_pointer_width = "64")]

pub mod iter;

use std::io::{Read, Write};
use std::ops::Range;

use anyhow::{anyhow, Result};

use crate::bit_vectors::{Access, BitVector, DArray, NumBits, Select};
use crate::broadword;
use crate::Serializable;
use iter::Iter;

const LINEAR_SCAN_THRESHOLD: usize = 64;

/// Compressed monotone increasing sequence through Elias-Fano encoding.
///
/// This implements an Elias-Fano representation for monotone increasing sequences.
/// When a sequence stores $`n`$ integers from $`[0, u-1]`$,
/// this representation takes $`n \lceil \log_2 \frac{u}{n} \rceil + 2n + o(n)`$ bits of space,
/// indicating that a sparse sequence can be stored in a very compressed space.
///
/// Another attraction of Elias-Fano is several search queries,
/// such as binary search, predecessor, and successor,
/// over the compressed representation.
///
/// # Example
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use sucds::mii_sequences::EliasFanoBuilder;
///
/// let mut efb = EliasFanoBuilder::new(8, 4)?;
/// efb.extend([1, 3, 3, 7])?;
/// let ef = efb.build();
///
/// assert_eq!(ef.len(), 4);
/// assert_eq!(ef.universe(), 8);
///
/// assert_eq!(ef.select(0), Some(1));
/// assert_eq!(ef.select(1), Some(3));
/// assert_eq!(ef.select(2), Some(3));
/// assert_eq!(ef.select(3), Some(7));
///
/// assert_eq!(ef.binsearch(7), Some(3));
/// assert_eq!(ef.binsearch(4), None);
///
/// // Builds an index to enable rank, predecessor, and successor.
/// let ef = ef.enable_rank();
///
/// assert_eq!(ef.rank(3), Some(1));
/// assert_eq!(ef.rank(4), Some(3));
/// assert_eq!(ef.predecessor(4), Some(3));
/// assert_eq!(ef.predecessor(3), Some(3));
/// assert_eq!(ef.successor(3), Some(3));
/// assert_eq!(ef.successor(4), Some(7));
/// # Ok(())
/// # }
/// ```
///
/// # Credits
///
/// This is a yet another Rust port of [succinct::elias_fano](https://github.com/ot/succinct/blob/master/elias_fano.hpp).
/// The implementation of binary search is based on that in
/// [tongrams::fast_ef_sequence](https://github.com/jermp/tongrams/blob/master/include/sequences/fast_ef_sequence.hpp).
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
    high_bits: DArray,
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
    /// An error is returned if
    ///
    ///  - `bits` is an empty stream, or
    ///  - `bits` contains no set bit.
    pub fn from_bits<I>(bits: I) -> Result<Self>
    where
        I: IntoIterator<Item = bool>,
    {
        let bv = BitVector::from_bits(bits);
        if bv.num_bits() == 0 {
            return Err(anyhow!("bits must not be empty."));
        }
        let n = bv.num_bits();
        let m = (0..bv.num_words()).fold(0, |acc, i| acc + broadword::popcount(bv.words()[i]));
        if m == 0 {
            return Err(anyhow!("bits must contains one set bit at least."));
        }
        let mut b = EliasFanoBuilder::new(n, m);
        for i in 0..n {
            if bv.access(i).unwrap() {
                b.push(i).unwrap();
            }
        }
        Ok(b.build())
    }

    /// Builds an index to enable operations [`Self::rank()`],
    /// [`Self::predecessor()`], and [`Self::successor()`].
    #[must_use]
    pub fn enable_rank(mut self) -> Self {
        self.high_bits = self.high_bits.enable_select0();
        self
    }

    /// Checks if [`Self::enable_rank()`] is set.
    #[inline(always)]
    pub const fn has_rank(&self) -> bool {
        self.high_bits.has_select0()
    }

    /// Gets the difference between the `k-1`-th and `k`-th integers
    /// (i.e., `select(k) - select(k-1)`), returning [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// Constant
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::mii_sequences::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.extend([1, 3, 3, 7])?;
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
        let high_val = self.high_bits.select1(k).unwrap();
        let low_val = self
            .low_bits
            .get_bits(k * self.low_len, self.low_len)
            .unwrap();
        let x = if k != 0 {
            ((high_val
                - self
                    .high_bits
                    .bit_vector()
                    .predecessor1(high_val - 1)
                    .unwrap()
                - 1)
                << self.low_len)
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
    /// $`O(\lg n)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::mii_sequences::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(11, 6)?;
    /// efb.extend([1, 3, 3, 6, 7, 10])?;
    /// let ef = efb.build();
    ///
    /// assert_eq!(ef.binsearch(6), Some(3));
    /// assert_eq!(ef.binsearch(10), Some(5));
    /// assert_eq!(ef.binsearch(9), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn binsearch(&self, val: usize) -> Option<usize> {
        // TODO(kampersanda): Implement Access.
        self.binsearch_range(0..self.len(), val)
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
    /// $`O(\lg |R|)`$ for the range $`R`$.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::mii_sequences::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(11, 6)?;
    /// efb.extend([1, 3, 3, 6, 7, 10])?;
    /// let ef = efb.build();
    ///
    /// assert_eq!(ef.binsearch_range(1..4, 6), Some(3));
    /// assert_eq!(ef.binsearch_range(5..6, 10), Some(5));
    /// assert_eq!(ef.binsearch_range(1..3, 6), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn binsearch_range(&self, range: Range<usize>, val: usize) -> Option<usize> {
        // TODO(kampersanda): Bound check.
        if range.is_empty() {
            return None;
        }

        // Binary search
        let (mut lo, mut hi) = (range.start, range.end);
        while hi - lo > LINEAR_SCAN_THRESHOLD {
            let mi = (lo + hi) / 2;
            let x = self.select(mi).unwrap();
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

    /// Returns the number of integers less than `pos`, or
    /// [`None`] if `self.universe() < pos`.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \frac{u}{n})`$
    ///
    /// # Panics
    ///
    /// It panics if the index is not built by [`Self::enable_rank()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::mii_sequences::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.extend([1, 3, 3, 7])?;
    /// let ef = efb.build().enable_rank();
    ///
    /// assert_eq!(ef.rank(3), Some(1));
    /// assert_eq!(ef.rank(4), Some(3));
    /// assert_eq!(ef.rank(8), Some(4));
    /// assert_eq!(ef.rank(9), None);
    /// # Ok(())
    /// # }
    /// ```
    pub fn rank(&self, pos: usize) -> Option<usize> {
        if self.universe() < pos {
            return None;
        }
        if self.universe() == pos {
            return Some(self.len());
        }

        let h_rank = pos >> self.low_len;
        let mut h_pos = self.high_bits.select0(h_rank).unwrap();
        let mut rank = h_pos - h_rank;
        let l_pos = pos & ((1 << self.low_len) - 1);

        while h_pos > 0
            && self.high_bits.access(h_pos - 1).unwrap()
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

    /// Returns the position of the `k`-th smallest integer, or
    /// [`None`] if `self.len() <= k`.
    ///
    /// # Complexity
    ///
    /// Constant
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::mii_sequences::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.extend([1, 3, 3, 7])?;
    /// let ef = efb.build();
    ///
    /// assert_eq!(ef.select(0), Some(1));
    /// assert_eq!(ef.select(1), Some(3));
    /// assert_eq!(ef.select(2), Some(3));
    /// assert_eq!(ef.select(3), Some(7));
    /// assert_eq!(ef.select(4), None);
    /// # Ok(())
    /// # }
    /// ```
    pub fn select(&self, k: usize) -> Option<usize> {
        if self.len() <= k {
            None
        } else {
            Some(
                ((self.high_bits.select1(k).unwrap() - k) << self.low_len)
                    | self
                        .low_bits
                        .get_bits(k * self.low_len, self.low_len)
                        .unwrap(),
            )
        }
    }

    /// Gets the largest element `pred` such that `pred <= pos`, or
    /// [`None`] if `self.universe() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Predecessor query.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \frac{u}{n})`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::mii_sequences::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.extend([1, 3, 3, 7])?;
    /// let ef = efb.build().enable_rank();
    ///
    /// assert_eq!(ef.predecessor(4), Some(3));
    /// assert_eq!(ef.predecessor(3), Some(3));
    /// assert_eq!(ef.predecessor(2), Some(1));
    /// assert_eq!(ef.predecessor(0), None);
    /// # Ok(())
    /// # }
    /// ```
    pub fn predecessor(&self, pos: usize) -> Option<usize> {
        if self.universe() <= pos {
            None
        } else {
            Some(self.rank(pos + 1).unwrap())
                .filter(|&i| i > 0)
                .map(|i| self.select(i - 1).unwrap())
        }
    }

    /// Gets the smallest element `succ` such that `succ >= pos`, or
    /// [`None`] if `self.universe() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Successor query.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \frac{u}{n})`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::mii_sequences::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.extend([1, 3, 3, 7])?;
    /// let ef = efb.build().enable_rank();
    ///
    /// assert_eq!(ef.successor(0), Some(1));
    /// assert_eq!(ef.successor(2), Some(3));
    /// assert_eq!(ef.successor(3), Some(3));
    /// assert_eq!(ef.successor(8), None);
    /// # Ok(())
    /// # }
    /// ```
    pub fn successor(&self, pos: usize) -> Option<usize> {
        if self.universe() <= pos {
            None
        } else {
            Some(self.rank(pos).unwrap())
                .filter(|&i| i < self.len())
                .map(|i| self.select(i).unwrap())
        }
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
    /// use sucds::mii_sequences::EliasFanoBuilder;
    ///
    /// let mut efb = EliasFanoBuilder::new(8, 4)?;
    /// efb.extend([1, 3, 3, 7])?;
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
    pub fn len(&self) -> usize {
        self.high_bits.num_ones()
    }

    /// Checks if the sequence is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the universe, i.e., the (exclusive) upper bound of possible integers.
    #[inline(always)]
    pub const fn universe(&self) -> usize {
        self.universe
    }
}

impl Serializable for EliasFano {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.high_bits.serialize_into(&mut writer)?;
        mem += self.low_bits.serialize_into(&mut writer)?;
        mem += self.low_len.serialize_into(&mut writer)?;
        mem += self.universe.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let high_bits = DArray::deserialize_from(&mut reader)?;
        let low_bits = BitVector::deserialize_from(&mut reader)?;
        let low_len = usize::deserialize_from(&mut reader)?;
        let universe = usize::deserialize_from(&mut reader)?;
        Ok(Self {
            high_bits,
            low_bits,
            low_len,
            universe,
        })
    }

    fn size_in_bytes(&self) -> usize {
        self.high_bits.size_in_bytes()
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
/// use sucds::mii_sequences::EliasFanoBuilder;
///
/// let mut efb = EliasFanoBuilder::new(8, 5)?;
///
/// assert_eq!(efb.universe(), 8);
/// assert_eq!(efb.num_vals(), 5);
///
/// efb.push(1)?;
/// efb.push(3)?;
/// efb.extend([3, 5, 7])?;
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
    pub fn new(universe: usize, num_vals: usize) -> Self {
        if num_vals == 0 {
            return Self {
                high_bits: BitVector::new(),
                low_bits: BitVector::new(),
                universe,
                num_vals,
                pos: 0,
                last: 0,
                low_len: 0,
            };
        }
        let low_len = broadword::msb(universe / num_vals).unwrap_or(0);
        Self {
            high_bits: BitVector::from_bit(false, (num_vals + 1) + (universe >> low_len) + 1),
            low_bits: BitVector::new(),
            universe,
            num_vals,
            pos: 0,
            last: 0,
            low_len,
        }
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
                "val must be no less than the last one {}, but got {val}.",
                self.last
            ));
        }
        if self.universe <= val {
            return Err(anyhow!(
                "val must be less than self.universe()={}, but got {val}.",
                self.universe
            ));
        }
        if self.num_vals <= self.pos {
            return Err(anyhow!(
                "The number of pushed integers must not exceed self.num_vals()={}.",
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
    pub fn extend<I>(&mut self, vals: I) -> Result<()>
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
            high_bits: DArray::from_bits(self.high_bits.iter()),
            low_bits: self.low_bits,
            low_len: self.low_len,
            universe: self.universe,
        }
    }

    /// Returns the universe, i.e., the (exclusive) upper bound of possible integers.
    #[inline(always)]
    pub const fn universe(&self) -> usize {
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

    #[test]
    fn test_from_bits_empty() {
        let e = EliasFano::from_bits([]);
    }

    #[test]
    fn test_from_bits_unset() {
        let e = EliasFano::from_bits([false, false, false]);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("bits must contains one set bit at least.".to_string())
        );
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let ef = EliasFano::from_bits([false, true, true, true, false, true])
            .unwrap()
            .enable_rank();
        let size = ef.serialize_into(&mut bytes).unwrap();
        let other = EliasFano::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(ef, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, ef.size_in_bytes());
    }

    #[test]
    fn test_builder_new_zero_size() {
        let e = EliasFanoBuilder::new(3, 0);
    }

    #[test]
    fn test_builder_push_decrease() {
        let mut b = EliasFanoBuilder::new(3, 2);
        b.push(2).unwrap();
        let e = b.push(1);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("val must be no less than the last one 2, but got 1.".to_string())
        );
    }

    #[test]
    fn test_builder_overflow_universe() {
        let mut b = EliasFanoBuilder::new(3, 2);
        let e = b.push(3);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("val must be less than self.universe()=3, but got 3.".to_string())
        );
    }

    #[test]
    fn test_builder_overflow_num_vals() {
        let mut b = EliasFanoBuilder::new(3, 1);
        b.push(1).unwrap();
        let e = b.push(2);
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("The number of pushed integers must not exceed self.num_vals()=1.".to_string())
        );
    }
}
