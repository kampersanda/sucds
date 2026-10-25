//! Compressed monotone increasing sequence through Elias-Fano encoding.

pub mod iter;

use core::ops::Range;

use crate::bit_vectors::{Access, BitVector, DArray, Select};
use crate::broadword;
use crate::io::{Read, Write};
use crate::serial::{Bytes, Shared, Source};
use crate::Result;
use crate::Serializable;
use crate::SucdsError;
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
/// # fn main() -> sucds::Result<()> {
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
    universe: u64,
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
        if bv.is_empty() {
            return Err(SucdsError::invalid_argument("bits must not be empty."));
        }
        let num_bits = bv.len();
        let num_ones = bv.num_ones();
        if num_ones == 0 {
            return Err(SucdsError::invalid_argument(
                "bits must contains one set bit at least.",
            ));
        }
        let mut builder = EliasFanoBuilder::new(num_bits as u64, num_ones)?;
        for pos in 0..num_bits {
            if bv.access(pos).unwrap() {
                builder.push(pos as u64)?;
            }
        }
        Ok(builder.build())
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
    /// # fn main() -> sucds::Result<()> {
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
    pub fn delta(&self, k: usize) -> Option<u64> {
        if self.len() <= k {
            return None;
        }
        let high_val = self.high_bits.select1(k).unwrap();
        let low_val = self
            .low_bits
            .get_bits(k * self.low_len, self.low_len)
            .unwrap();
        let delta = if k != 0 {
            (((high_val
                - self
                    .high_bits
                    .bit_vector()
                    .predecessor1(high_val - 1)
                    .unwrap()
                - 1) as u64)
                << self.low_len)
                + low_val
                - self
                    .low_bits
                    .get_bits((k - 1) * self.low_len, self.low_len)
                    .unwrap()
        } else {
            (((high_val - k) as u64) << self.low_len) | low_val
        };
        Some(delta)
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
    /// # fn main() -> sucds::Result<()> {
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
    pub fn binsearch(&self, val: u64) -> Option<usize> {
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
    /// # fn main() -> sucds::Result<()> {
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
    pub fn binsearch_range(&self, range: Range<usize>, val: u64) -> Option<usize> {
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

    /// Returns the number of integers less than `val`, or
    /// [`None`] if `self.universe() < val`.
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
    /// # fn main() -> sucds::Result<()> {
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
    pub fn rank(&self, val: u64) -> Option<usize> {
        if self.universe() < val {
            return None;
        }
        if self.universe() == val {
            return Some(self.len());
        }

        let high_val = (val >> self.low_len) as usize;
        let low_val = val & ((1 << self.low_len) - 1);

        let mut high_pos = self.high_bits.select0(high_val).unwrap();
        let mut rank = high_pos - high_val;

        while high_pos > 0
            && self.high_bits.access(high_pos - 1).unwrap()
            && self
                .low_bits
                .get_bits((rank - 1) * self.low_len, self.low_len)
                .unwrap()
                >= low_val
        {
            rank -= 1;
            high_pos -= 1;
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
    /// # fn main() -> sucds::Result<()> {
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
    pub fn select(&self, k: usize) -> Option<u64> {
        if self.len() <= k {
            None
        } else {
            Some(
                (((self.high_bits.select1(k).unwrap() - k) as u64) << self.low_len)
                    | self
                        .low_bits
                        .get_bits(k * self.low_len, self.low_len)
                        .unwrap(),
            )
        }
    }

    /// Gets the largest element `pred` such that `pred <= val`, or
    /// [`None`] if `self.universe() <= val`.
    ///
    /// # Arguments
    ///
    /// - `val`: Predecessor query.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \frac{u}{n})`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> sucds::Result<()> {
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
    pub fn predecessor(&self, val: u64) -> Option<u64> {
        if self.universe() <= val {
            None
        } else {
            Some(self.rank(val + 1).unwrap())
                .filter(|&i| i > 0)
                .map(|i| self.select(i - 1).unwrap())
        }
    }

    /// Gets the smallest element `succ` such that `succ >= val`, or
    /// [`None`] if `self.universe() <= val`.
    ///
    /// # Arguments
    ///
    /// - `val`: Successor query.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \frac{u}{n})`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> sucds::Result<()> {
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
    pub fn successor(&self, val: u64) -> Option<u64> {
        if self.universe() <= val {
            None
        } else {
            Some(self.rank(val).unwrap())
                .filter(|&i| i < self.len())
                .map(|i| self.select(i).unwrap())
        }
    }

    /// Creates an iterator of [`Iter`] to enumerate integers from the `k`-th one.
    ///
    /// # Arguments
    ///
    /// - `k`: Position to start enumeration.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> sucds::Result<()> {
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
    pub fn iter(&self, k: usize) -> Iter<'_> {
        Iter::new(self, k)
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.high_bits.num_ones()
    }

    /// Checks if the sequence is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the universe, i.e., the (exclusive) upper bound of possible integers.
    #[inline(always)]
    pub const fn universe(&self) -> u64 {
        self.universe
    }
}

impl EliasFano {
    /// Deserializes the sequence and checks the consistency of its fields.
    fn deserialize_with<Src: Source>(src: &mut Src, checked: bool) -> Result<Self> {
        let high_bits: DArray = src.read(checked)?;
        let low_bits: BitVector = src.read(checked)?;
        let low_len: usize = src.read(checked)?;
        let universe: u64 = src.read(checked)?;
        if low_len >= 64 {
            return Err(SucdsError::invalid_data(format!(
                "low_len must be less than 64, but got {low_len}."
            )));
        }
        let len = high_bits.num_ones();
        if len.checked_mul(low_len) != Some(low_bits.len()) {
            return Err(SucdsError::invalid_data(format!(
                "The number of low bits must be len*low_len={len}*{low_len}, but got {}.",
                low_bits.len()
            )));
        }
        // rank(val) for val < universe needs the unset bit for the high part of val.
        if let Some(max_val) = universe.checked_sub(1) {
            if (high_bits.len() - len) as u64 <= max_val >> low_len {
                return Err(SucdsError::invalid_data(format!(
                    "The high bits must have more than {} unset bits, but got {}.",
                    max_val >> low_len,
                    high_bits.len() - len
                )));
            }
        }
        let ef = Self {
            high_bits,
            low_bits,
            low_len,
            universe,
        };
        // High parts never decrease, so the largest value is in the last high bucket,
        // whose low parts can be in any order.
        if let Some(last) = len.checked_sub(1) {
            let high = |k| ef.high_bits.select1(k).unwrap() - k;
            let last_high = high(last);
            // Checking the high part first keeps `select` from wrapping around in the shift.
            let mut last_bucket = (0..len).rev().take_while(|&k| high(k) == last_high);
            if last_high as u64 > universe >> low_len
                || last_bucket.any(|k| ef.select(k).unwrap() >= universe)
            {
                return Err(SucdsError::invalid_data(format!(
                    "Values must be less than universe={universe}."
                )));
            }
        }
        Ok(ef)
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

    /// Deserializes the sequence and checks its consistency.
    ///
    /// # Complexity
    ///
    /// $`O(n + n\ell)`$, where $`n`$ is the number of integers and $`\ell`$ is the number of low bits per integer.
    /// It includes rebuilding the indexes of the high bits, which have $`O(n)`$ bits,
    /// and checking the integers in the last high bucket.
    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        Self::deserialize_with(&mut reader, true)
    }

    /// Deserializes the sequence without checking the indexes of the high bits.
    ///
    /// # Complexity
    ///
    /// $`O(n + n\ell)`$, where $`n`$ is the number of integers and $`\ell`$ is the number of low bits per integer.
    /// It skips rebuilding the indexes of the high bits, but still checks the integers in the last high bucket.
    fn deserialize_from_unchecked<R: Read>(mut reader: R) -> Result<Self> {
        Self::deserialize_with(&mut reader, false)
    }

    /// Deserializes the data structure from the shared bytes in the same manner as
    /// [`Self::deserialize_from()`], sharing its arrays with `bytes`.
    ///
    /// # Complexity
    ///
    /// That of [`Self::deserialize_from()`], except that the arrays are shared in constant time.
    fn deserialize_from_bytes(bytes: &mut Bytes) -> Result<Self> {
        Self::deserialize_with(&mut Shared(bytes), true)
    }

    /// Deserializes the data structure from the shared bytes in the same manner as
    /// [`Self::deserialize_from_unchecked()`], sharing its arrays with `bytes`.
    ///
    /// # Complexity
    ///
    /// That of [`Self::deserialize_from_unchecked()`], except that the arrays are shared in constant time.
    fn deserialize_from_bytes_unchecked(bytes: &mut Bytes) -> Result<Self> {
        Self::deserialize_with(&mut Shared(bytes), false)
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
/// # fn main() -> sucds::Result<()> {
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
    universe: u64,
    num_vals: usize,
    num_pushed: usize,
    last: u64,
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
    pub fn new(universe: u64, num_vals: usize) -> Result<Self> {
        if num_vals == 0 {
            return Err(SucdsError::invalid_argument("num_vals must not be zero."));
        }
        let low_len = broadword::msb(universe / num_vals as u64).unwrap_or(0);
        Ok(Self {
            high_bits: BitVector::from_bit(
                false,
                (num_vals + 1) + (universe >> low_len) as usize + 1,
            ),
            low_bits: BitVector::new(),
            universe,
            num_vals,
            num_pushed: 0,
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
    pub fn push(&mut self, val: u64) -> Result<()> {
        if val < self.last {
            return Err(SucdsError::invalid_argument(format!(
                "val must be no less than the last one {}, but got {val}.",
                self.last
            )));
        }
        if self.universe <= val {
            return Err(SucdsError::invalid_argument(format!(
                "val must be less than self.universe()={}, but got {val}.",
                self.universe
            )));
        }
        if self.num_vals <= self.num_pushed {
            return Err(SucdsError::invalid_state(format!(
                "The number of pushed integers must not exceed self.num_vals()={}.",
                self.num_vals
            )));
        }

        self.last = val;
        let low_mask = (1 << self.low_len) - 1;
        if self.low_len != 0 {
            self.low_bits
                .push_bits(val & low_mask, self.low_len)
                .unwrap();
        }
        self.high_bits
            .set_bit((val >> self.low_len) as usize + self.num_pushed, true)
            .unwrap();
        self.num_pushed += 1;

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
        I: IntoIterator<Item = u64>,
    {
        for val in vals {
            self.push(val)?;
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
    pub const fn universe(&self) -> u64 {
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
        assert!(matches!(e, Err(SucdsError::InvalidArgument(_))));
    }

    #[test]
    fn test_from_bits_unset() {
        let e = EliasFano::from_bits([false, false, false]);
        assert!(matches!(e, Err(SucdsError::InvalidArgument(_))));
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

    fn serialized_example() -> alloc::vec::Vec<u8> {
        let mut b = EliasFanoBuilder::new(65, 4).unwrap();
        b.extend([0, 2, 4, 64]).unwrap();
        let mut bytes = vec![];
        b.build().serialize_into(&mut bytes).unwrap();
        bytes
    }

    #[test]
    fn test_deserialize_unchecked() {
        let mut b = EliasFanoBuilder::new(10_000, 1000).unwrap();
        b.extend((0..1000).map(|i| i * 7)).unwrap();
        let efs = vec![b.build().enable_rank()];
        let mut bytes = vec![];
        efs.serialize_into(&mut bytes).unwrap();
        let other = alloc::vec::Vec::<EliasFano>::deserialize_from_unchecked(&bytes[..]).unwrap();
        assert_eq!(efs, other);
    }

    #[test]
    fn test_deserialize_huge_len() {
        let mut bytes = serialized_example();
        bytes[0..8].copy_from_slice(&(1u64 << 43).to_le_bytes());
        let e = EliasFano::deserialize_from(&bytes[..]);
        assert!(e.is_err());
    }

    #[test]
    fn test_deserialize_inconsistent_low_len() {
        let mut bytes = serialized_example();
        let n = bytes.len();
        bytes[n - 16..n - 8].copy_from_slice(&40u64.to_le_bytes());
        let e = EliasFano::deserialize_from(&bytes[..]);
        assert!(matches!(e, Err(SucdsError::InvalidData(_))));
    }

    #[test]
    fn test_deserialize_inconsistent_universe() {
        let mut bytes = serialized_example();
        let n = bytes.len();
        bytes[n - 8..].copy_from_slice(&u64::MAX.to_le_bytes());
        let e = EliasFano::deserialize_from(&bytes[..]);
        assert!(matches!(e, Err(SucdsError::InvalidData(_))));
    }

    fn serialize_raw(
        high_bits: &[bool],
        low_bits: &[bool],
        low_len: usize,
        universe: u64,
    ) -> alloc::vec::Vec<u8> {
        let ef = EliasFano {
            high_bits: DArray::from_bits(high_bits.iter().copied()),
            low_bits: BitVector::from_bits(low_bits.iter().copied()),
            low_len,
            universe,
        };
        let mut bytes = vec![];
        ef.serialize_into(&mut bytes).unwrap();
        bytes
    }

    #[test]
    fn test_deserialize_high_part_beyond_universe() {
        // select(0) would be 3 >= universe = 2.
        let bytes = serialize_raw(&[false, false, false, true, false], &[], 0, 2);
        let e = EliasFano::deserialize_from(&bytes[..]);
        assert!(matches!(e, Err(SucdsError::InvalidData(_))));
    }

    #[test]
    fn test_deserialize_low_part_beyond_universe() {
        // Values are [4, 5], both in the last high bucket, and 5 >= universe = 5.
        let bytes = serialize_raw(
            &[false, false, true, true, false, false, false],
            &[false, true],
            1,
            5,
        );
        let e = EliasFano::deserialize_from(&bytes[..]);
        assert!(matches!(e, Err(SucdsError::InvalidData(_))));
    }

    #[test]
    fn test_deserialize_wrapping_value() {
        // The value is 2^64, which wraps to 0 when decoded.
        let bytes = serialize_raw(&[false, false, true], &[false; 63], 63, 1);
        let e = EliasFano::deserialize_from(&bytes[..]);
        assert!(matches!(e, Err(SucdsError::InvalidData(_))));
    }

    #[test]
    fn test_builder_new_zero_size() {
        let e = EliasFanoBuilder::new(3, 0);
        assert!(matches!(e, Err(SucdsError::InvalidArgument(_))));
    }

    #[test]
    fn test_builder_push_decrease() {
        let mut b = EliasFanoBuilder::new(3, 2).unwrap();
        b.push(2).unwrap();
        let e = b.push(1);
        assert!(matches!(e, Err(SucdsError::InvalidArgument(_))));
    }

    #[test]
    fn test_builder_overflow_universe() {
        let mut b = EliasFanoBuilder::new(3, 2).unwrap();
        let e = b.push(3);
        assert!(matches!(e, Err(SucdsError::InvalidArgument(_))));
    }

    #[test]
    fn test_builder_overflow_num_vals() {
        let mut b = EliasFanoBuilder::new(3, 1).unwrap();
        b.push(1).unwrap();
        let e = b.push(2);
        assert!(matches!(e, Err(SucdsError::InvalidState(_))));
    }
}
