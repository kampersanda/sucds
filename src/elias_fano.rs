#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};
use std::mem::size_of;

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use crate::{broadword, darray::DArrayIndex, BitVector};

/// Compressed monotone increasing sequence through Elias-Fano encoding.
///
/// [`EliasFano`] implements an Elias-Fano representation for monotone increasing sequences.
/// When a sequence stores $`n`$ integers from $`[0, u-1]`$, this representation takes $`n \lceil \log_2 \frac{u}{n} \rceil + 2n`$ bits of space.
/// That is, a sparse sequence can be stored in a very compressed space.
///
/// This is a yet another Rust port of [succinct::elias_fano](https://github.com/ot/succinct/blob/master/elias_fano.hpp).
///
/// # Example
///
/// ```
/// use sucds::{EliasFano, EliasFanoBuilder};
///
/// let mut b = EliasFanoBuilder::new(10, 4).unwrap();
/// b.append(&[2, 3, 6, 9]).unwrap();
///
/// let ef = EliasFano::new(b, true);
/// assert_eq!(ef.select(1), 3);
/// assert_eq!(ef.select(3), 9);
///
/// assert_eq!(ef.rank(5), 2);
/// assert_eq!(ef.rank(10), 4);
///
/// assert_eq!(ef.predecessor(5), Some(3));
/// assert_eq!(ef.predecessor(1), None);
///
/// assert_eq!(ef.successor(4), Some(6));
/// assert_eq!(ef.successor(10), None);
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
#[derive(Default, Debug, PartialEq, Eq)]
pub struct EliasFano {
    high_bits: BitVector,
    high_bits_d1: DArrayIndex,
    high_bits_d0: Option<DArrayIndex>,
    low_bits: BitVector,
    low_len: usize,
    universe: usize,
}

impl EliasFano {
    /// Creates a new [`EliasFano`] from builder `b`.
    ///
    /// # Arguments
    ///
    /// - `b`: Builder.
    /// - `with_rank_index`: Flag to build the index for rank, predecessor and successor.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{EliasFano, EliasFanoBuilder};
    ///
    /// let mut b = EliasFanoBuilder::new(10, 4).unwrap();
    /// b.append(&[2, 3, 6, 9]).unwrap();
    ///
    /// let ef = EliasFano::new(b, false);
    /// assert_eq!(ef.select(0), 2);
    /// assert_eq!(ef.select(1), 3);
    /// assert_eq!(ef.select(2), 6);
    /// assert_eq!(ef.select(3), 9);
    /// ```
    pub fn new(b: EliasFanoBuilder, with_rank_index: bool) -> Self {
        let high_bits_d1 = DArrayIndex::new(&b.high_bits, true);
        let high_bits_d0 = if with_rank_index {
            Some(DArrayIndex::new(&b.high_bits, false))
        } else {
            None
        };
        Self {
            high_bits: b.high_bits,
            high_bits_d1,
            high_bits_d0,
            low_bits: b.low_bits,
            low_len: b.low_len,
            universe: b.universe,
        }
    }

    /// Creates a new [`EliasFano`] from input bitset `bits`.
    ///
    /// # Arguments
    ///
    /// - `bits`: List of bits.
    /// - `with_rank_index`: Flag to build the index for rank, predecessor and successor.
    ///
    /// # Errors
    ///
    /// `anyhow::Error` will be returned if `bits` contains no set bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::EliasFano;
    ///
    /// let ef = EliasFano::from_bits(&[true, false, false, true], true).unwrap();
    /// assert_eq!(ef.rank(2), 1);
    /// assert_eq!(ef.select(1), 3);
    /// assert_eq!(ef.predecessor(2), Some(0));
    /// assert_eq!(ef.successor(1), Some(3));
    /// ```
    pub fn from_bits<'a, I>(bits: I, with_rank_index: bool) -> Result<Self>
    where
        I: IntoIterator<Item = &'a bool>,
    {
        Self::from_bitvec(&BitVector::from_bits(bits), with_rank_index)
    }

    /// Creates a new [`EliasFano`] from input bit vector `bv`.
    ///
    /// # Arguments
    ///
    /// - `bv`: Input bit vector.
    /// - `with_rank_index`: Flag to build the index for rank, predecessor and successor.
    ///
    /// # Errors
    ///
    /// `anyhow::Error` will be returned if `bv` contains no set bit.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{EliasFano, BitVector};
    ///
    /// let bv = BitVector::from_bits(&[true, false, false, true]);
    /// let ef = EliasFano::from_bitvec(&bv, true).unwrap();
    /// assert_eq!(ef.rank(2), 1);
    /// assert_eq!(ef.select(1), 3);
    /// assert_eq!(ef.predecessor(2), Some(0));
    /// assert_eq!(ef.successor(1), Some(3));
    /// ```
    pub fn from_bitvec(bv: &BitVector, with_rank_index: bool) -> Result<Self> {
        let n = bv.len();
        let m = (0..bv.num_words())
            .into_iter()
            .fold(0, |acc, i| acc + broadword::popcount(bv.get_word(i)));
        let mut b = EliasFanoBuilder::new(n, m)?;
        for i in 0..n {
            if bv.get_bit(i) {
                b.push(i)?;
            }
        }
        Ok(Self::new(b, with_rank_index))
    }

    /// Searches the `k`-th iteger.
    ///
    /// # Arguments
    ///
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::EliasFano;
    ///
    /// let ef = EliasFano::from_bits(&[true, false, false, true], false).unwrap();
    /// assert_eq!(ef.select(0), 0);
    /// assert_eq!(ef.select(1), 3);
    /// ```
    #[inline(always)]
    pub fn select(&self, k: usize) -> usize {
        ((self.high_bits_d1.select(&self.high_bits, k) - k) << self.low_len)
            | self.low_bits.get_bits(k * self.low_len, self.low_len)
    }

    /// Counts the number of integers less than `pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Rank query.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \frac{u}{n})`$
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::EliasFano;
    ///
    /// let ef = EliasFano::from_bits(&[true, false, false, true], true).unwrap();
    /// assert_eq!(ef.rank(1), 1);
    /// assert_eq!(ef.rank(2), 1);
    /// assert_eq!(ef.rank(3), 1);
    /// assert_eq!(ef.rank(4), 2);
    /// ```
    #[inline(always)]
    pub fn rank(&self, pos: usize) -> usize {
        debug_assert!(self.high_bits_d0.is_some());

        if pos > self.universe() {
            return self.len();
        }

        let high_bits_d0 = self.high_bits_d0.as_ref().unwrap();

        let h_rank = pos >> self.low_len;
        let mut h_pos = high_bits_d0.select(&self.high_bits, h_rank);
        let mut rank = h_pos - h_rank;
        let l_pos = pos & ((1 << self.low_len) - 1);

        while h_pos > 0
            && self.high_bits.get_bit(h_pos - 1)
            && self
                .low_bits
                .get_bits((rank - 1) * self.low_len, self.low_len)
                >= l_pos
        {
            rank -= 1;
            h_pos -= 1;
        }

        rank
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
    /// use sucds::EliasFano;
    ///
    /// let ef = EliasFano::from_bits(&[false, true, false, false, true], true).unwrap();
    /// assert_eq!(ef.predecessor(4), Some(4));
    /// assert_eq!(ef.predecessor(3), Some(1));
    /// assert_eq!(ef.predecessor(0), None);
    /// ```
    #[inline(always)]
    pub fn predecessor(&self, pos: usize) -> Option<usize> {
        Some(self.rank(pos + 1))
            .filter(|&i| i > 0)
            .map(|i| self.select(i - 1))
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
    /// use sucds::EliasFano;
    ///
    /// let ef = EliasFano::from_bits(&[true, false, false, true, false], true).unwrap();
    /// assert_eq!(ef.successor(0), Some(0));
    /// assert_eq!(ef.successor(1), Some(3));
    /// assert_eq!(ef.successor(4), None);
    /// ```
    #[inline(always)]
    pub fn successor(&self, pos: usize) -> Option<usize> {
        Some(self.rank(pos))
            .filter(|&i| i < self.len())
            .map(|i| self.select(i))
    }

    /// Gets the difference between the `k-1`-th and `k`-th integers
    /// (i.e., `select(k) - select(k-1)`).
    ///
    /// # Arguments
    ///
    /// - `k`: Select query.
    ///
    /// # Complexity
    ///
    /// - Constant
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::EliasFano;
    ///
    /// let ef = EliasFano::from_bits(&[false, true, false, false, true], false).unwrap();
    /// assert_eq!(ef.delta(0), 1);
    /// assert_eq!(ef.delta(1), 3);
    /// ```
    #[inline(always)]
    pub fn delta(&self, k: usize) -> usize {
        let high_val = self.high_bits_d1.select(&self.high_bits, k);
        let low_val = self.low_bits.get_bits(k * self.low_len, self.low_len);
        if k != 0 {
            ((high_val - self.high_bits.predecessor1(high_val - 1).unwrap() - 1) << self.low_len)
                + low_val
                - self.low_bits.get_bits((k - 1) * self.low_len, self.low_len)
        } else {
            ((high_val - k) << self.low_len) | low_val
        }
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

    /// Gets the (exclusive) upper bound of integers.
    #[inline(always)]
    pub const fn universe(&self) -> usize {
        self.universe
    }

    pub fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = self.high_bits.serialize_into(&mut writer)?;
        mem += self.high_bits_d1.serialize_into(&mut writer)?;
        if let Some(high_bits_d0) = &self.high_bits_d0 {
            writer.write_u8(1)?;
            mem += high_bits_d0.serialize_into(&mut writer)?;
        } else {
            writer.write_u8(0)?;
        }
        mem += self.low_bits.serialize_into(&mut writer)?;
        writer.write_u64::<LittleEndian>(self.low_len as u64)?;
        writer.write_u64::<LittleEndian>(self.universe as u64)?;
        Ok(mem + size_of::<u8>() + size_of::<u64>() + size_of::<u64>())
    }

    pub fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let high_bits = BitVector::deserialize_from(&mut reader)?;
        let high_bits_d1 = DArrayIndex::deserialize_from(&mut reader)?;
        let high_bits_d0 = if reader.read_u8()? != 0 {
            Some(DArrayIndex::deserialize_from(&mut reader)?)
        } else {
            None
        };
        let low_bits = BitVector::deserialize_from(&mut reader)?;
        let low_len = reader.read_u64::<LittleEndian>()? as usize;
        let universe = reader.read_u64::<LittleEndian>()? as usize;
        Ok(Self {
            high_bits,
            high_bits_d1,
            high_bits_d0,
            low_bits,
            low_len,
            universe,
        })
    }

    pub fn size_in_bytes(&self) -> usize {
        self.high_bits.size_in_bytes()
            + self.high_bits_d1.size_in_bytes()
            + size_of::<u8>()
            + self
                .high_bits_d0
                .as_ref()
                .map_or(0, |high_bits_d0| high_bits_d0.size_in_bytes())
            + self.low_bits.size_in_bytes()
            + size_of::<u64>()
            + size_of::<u64>()
    }
}

/// Builder of EliasFano.
pub struct EliasFanoBuilder {
    high_bits: BitVector,
    low_bits: BitVector,
    universe: usize,
    num_ints: usize,
    pos: usize,
    last: usize,
    low_len: usize,
}

impl EliasFanoBuilder {
    /// Creates a new [`EliasFanoBuilder`].
    ///
    /// # Arguments
    ///
    /// - `universe`: The (exclusive) upper bound of integers to be stored, i.e., an integer in `[0..universe - 1]`.
    /// - `num_ints`: The number of integers to be stored (> 0).
    ///
    /// # Errors
    ///
    /// `anyhow::Error` will be returned if the given setting is invalid.
    pub fn new(universe: usize, num_ints: usize) -> Result<Self> {
        if num_ints == 0 {
            return Err(anyhow!("num_ints must not be zero"));
        }
        let low_len = broadword::msb(universe / num_ints).unwrap_or(0);
        Ok(Self {
            high_bits: BitVector::with_len((num_ints + 1) + (universe >> low_len) + 1),
            low_bits: BitVector::new(),
            universe,
            num_ints,
            pos: 0,
            last: 0,
            low_len,
        })
    }

    /// Pushes integer `i` at the end.
    ///
    /// # Arguments
    ///
    /// - `i`: Pushed integer that must be no less than the last one.
    ///
    /// # Errors
    ///
    /// `anyhow::Error` will be returned if the input integer is invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use sucds::{EliasFano, EliasFanoBuilder};
    ///
    /// let mut b = EliasFanoBuilder::new(10, 4).unwrap();
    /// [2, 3, 6, 9].iter().for_each(|&x| b.push(x).unwrap());
    ///
    /// let ef = EliasFano::new(b, false);
    /// assert_eq!(ef.select(0), 2);
    /// assert_eq!(ef.select(1), 3);
    /// assert_eq!(ef.select(2), 6);
    /// assert_eq!(ef.select(3), 9);
    /// ```
    pub fn push(&mut self, i: usize) -> Result<()> {
        if i < self.last {
            return Err(anyhow!(
                "The input integer {} must be no less than the last one {}",
                i,
                self.last
            ));
        }
        if self.universe <= i {
            return Err(anyhow!(
                "The input integer {} must be less than the universe {}",
                i,
                self.universe
            ));
        }
        if self.num_ints <= self.pos {
            return Err(anyhow!(
                "The number of stored integers exceeds the given upper bound {}",
                self.num_ints
            ));
        }

        self.last = i;
        let low_mask = (1 << self.low_len) - 1;
        if self.low_len != 0 {
            self.low_bits.push_bits(i & low_mask, self.low_len);
        }
        self.high_bits.set_bit((i >> self.low_len) + self.pos, true);
        self.pos += 1;

        Ok(())
    }

    /// Appends integers at the end.
    ///
    /// # Arguments
    ///
    /// - `ints`: Pushed integers that are increasing.
    ///
    /// # Errors
    ///
    /// `anyhow::Error` will be returned if the input integers are invalid.
    ///
    /// # Example
    ///
    /// ```
    /// use sucds::{EliasFano, EliasFanoBuilder};
    ///
    /// let mut b = EliasFanoBuilder::new(10, 4).unwrap();
    /// b.append(&[2, 3, 6, 9]).unwrap();
    ///
    /// let ef = EliasFano::new(b, false);
    /// assert_eq!(ef.select(0), 2);
    /// assert_eq!(ef.select(1), 3);
    /// assert_eq!(ef.select(2), 6);
    /// assert_eq!(ef.select(3), 9);
    /// ```
    pub fn append<'a, I>(&mut self, ints: I) -> Result<()>
    where
        I: IntoIterator<Item = &'a usize>,
    {
        for &x in ints {
            self.push(x)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    fn gen_random_bits(len: usize, seed: u64) -> Vec<bool> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen::<bool>()).collect()
    }

    fn test_rank_select(bits: &[bool], ef: &EliasFano) {
        let mut cur_rank = 0;
        for i in 0..bits.len() {
            assert_eq!(cur_rank, ef.rank(i));
            if bits[i] {
                assert_eq!(i, ef.select(cur_rank));
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

    #[test]
    fn test_tiny_bits() {
        let ef =
            EliasFano::from_bits(&[true, false, false, true, false, true, true], false).unwrap();
        assert_eq!(ef.select(0), 0);
        assert_eq!(ef.select(1), 3);
        assert_eq!(ef.select(2), 5);
        assert_eq!(ef.select(3), 6);
    }

    #[test]
    fn test_random_bits() {
        for seed in 0..100 {
            let bits = gen_random_bits(10000, seed);
            let ef = EliasFano::from_bits(&bits, true).unwrap();
            test_rank_select(&bits, &ef);
            test_successor_predecessor(&bits, &ef);
        }
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let ef = EliasFano::from_bits(&gen_random_bits(10000, 42), true).unwrap();
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
        b.append(&[1, 2, 3, 4, 5]).unwrap();
    }

    #[test]
    #[should_panic]
    fn test_non_increasing() {
        let mut b = EliasFanoBuilder::new(10, 4).unwrap();
        b.append(&[1, 2, 3, 2]).unwrap();
    }
}
