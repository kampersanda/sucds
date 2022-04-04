//! Time- and space-efficient data structure for a sequence of integers,
//! supporting some queries such as ranking, selection, and intersection.
#![cfg(target_pointer_width = "64")]

pub mod iter;

use std::io::{Read, Write};
use std::mem::size_of;
use std::ops::Range;

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

use crate::wavelet_matrix::iter::Iter;
use crate::{broadword, BitVector, RsBitVector, Searial};

/// Time- and space-efficient data structure for a sequence of integers,
/// supporting some queries such as ranking, selection, and intersection.
///
/// [`WaveletMatrix`] stores a sequence of integers and provides myriad operations on the sequence.
/// When a sequence stores $`n`$ integers from $`[0, \sigma -1]`$,
/// most of the operations run in $`O(\log \sigma)`$ , using  $`n \log \sigma + o (n \log \sigma ) + O(\log \sigma \log n)`$ bits.
///
/// This is a yet another Rust port of [hillbig's waveletMatrix](https://github.com/hillbig/waveletTree/blob/master/waveletMatrix.go).
///
/// # Examples
///
/// ```
/// use sucds::WaveletMatrix;
///
/// let text = "tobeornottobethatisthequestion";
/// let wm = WaveletMatrix::from_ints(text.chars().map(|c| c as usize)).unwrap();
///
/// assert_eq!(wm.len(), text.chars().count());
/// assert_eq!(wm.dim(), 'u' as usize + 1);
///
/// assert_eq!(wm.get(20), 'h' as usize);
/// assert_eq!(wm.rank(22, 'o' as usize), 4);
/// assert_eq!(wm.select(2, 't' as usize), 9);
/// ```
///
/// # References
///
/// - F. Claude, and G. Navarro, "The Wavelet Matrix," In SPIRE 2012.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct WaveletMatrix {
    layers: Vec<RsBitVector>,
    dim: usize,
    len: usize,
    width: usize,
}

impl WaveletMatrix {
    /// Builds a [`WaveletMatrix`] from an iterator of integers.
    ///
    /// # Arguments
    ///
    /// - `ints`: Iterator of integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::WaveletMatrix;
    ///
    /// let ints = vec![20, 7, 13, 2, 11];
    /// let wm = WaveletMatrix::from_ints(ints.iter().cloned()).unwrap();
    ///
    /// assert_eq!(wm.get(2), 13);
    /// assert_eq!(wm.len(), ints.len());
    /// assert_eq!(wm.dim(), 21);
    /// ```
    pub fn from_ints<I>(ints: I) -> Result<Self>
    where
        I: IntoIterator<Item = usize>,
    {
        let mut wmb = WaveletMatrixBuilder::default();
        for v in ints {
            wmb.push(v);
        }
        wmb.build()
    }

    /// Gets the maximum value + 1 in stored integers.
    #[inline(always)]
    pub const fn dim(&self) -> usize {
        self.dim
    }

    /// Gets the number of intergers stored.
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Checks if the list of intergers is empty.
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the maximum number of bits needed to be stored for each integers.
    #[inline(always)]
    pub const fn width(&self) -> usize {
        self.width
    }

    /// Gets the integer located at `pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position to get.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::WaveletMatrix;
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_ints(text.chars().map(|c| c as usize)).unwrap();
    ///
    /// assert_eq!(wm.get(2), 'b' as usize);
    /// assert_eq!(wm.get(5), 'r' as usize);
    /// assert_eq!(wm.get(20), 'h' as usize);
    /// ```
    #[inline(always)]
    pub fn get(&self, mut pos: usize) -> usize {
        let mut val = 0;
        for depth in 0..self.width as usize {
            val <<= 1;
            let rsbv = &self.layers[depth];
            if rsbv.get_bit(pos) {
                val |= 1;
                pos = rsbv.rank1(pos) + rsbv.num_zeros();
            } else {
                pos = rsbv.rank0(pos);
            }
        }
        val
    }

    /// Gets the number of occurrence of `val` in [0, `pos`).
    ///
    /// # Arguments
    ///
    /// - `pos`: Position to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::WaveletMatrix;
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_ints(text.chars().map(|c| c as usize)).unwrap();
    ///
    /// assert_eq!(wm.rank(14, 'b' as usize), 2);
    /// assert_eq!(wm.rank(14, 'o' as usize), 4);
    /// assert_eq!(wm.rank(14, 'w' as usize), 0);
    /// ```
    #[inline(always)]
    pub fn rank(&self, pos: usize, val: usize) -> usize {
        self.rank_range(0..pos, val)
    }

    /// Gets the number of occurrence of `val` in the given `range`.
    ///
    /// # Arguments
    ///
    /// - `range`: Position to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::WaveletMatrix;
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_ints(text.chars().map(|c| c as usize)).unwrap();
    ///
    /// assert_eq!(wm.rank_range(0..14, 'o' as usize), 4);
    /// assert_eq!(wm.rank_range(14..20, 'a' as usize), 1);
    /// assert_eq!(wm.rank_range(20..24, 'b' as usize), 0);
    /// ```
    #[inline]
    pub fn rank_range(&self, range: Range<usize>, val: usize) -> usize {
        let mut start_pos = range.start;
        let mut end_pos = range.end;
        for depth in 0..self.width as usize {
            let bit = Self::get_msb(val, depth, self.width);
            let rsbv = &self.layers[depth];
            if bit {
                start_pos = rsbv.rank1(start_pos) + rsbv.num_zeros();
                end_pos = rsbv.rank1(end_pos) + rsbv.num_zeros();
            } else {
                start_pos = rsbv.rank0(start_pos);
                end_pos = rsbv.rank0(end_pos);
            }
        }
        (start_pos..end_pos).len()
    }

    /// Gets the occurrence position of `k`-th `val` in [0, n).
    ///
    /// # Arguments
    ///
    /// - `k`: Rank to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::WaveletMatrix;
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_ints(text.chars().map(|c| c as usize)).unwrap();
    ///
    /// assert_eq!(wm.select(2, 't' as usize), 9);
    /// assert_eq!(wm.select(0, 'q' as usize), 22);
    /// ```
    #[inline(always)]
    pub fn select(&self, k: usize, val: usize) -> usize {
        self.select_helper(k, val, 0, 0)
    }

    #[inline]
    fn select_helper(&self, mut k: usize, val: usize, mut pos: usize, depth: usize) -> usize {
        if depth == self.width {
            return pos + k;
        }
        let bit = Self::get_msb(val, depth, self.width);
        let rsbv = &self.layers[depth];
        if bit {
            let zeros = rsbv.num_zeros();
            pos = rsbv.rank1(pos) + zeros;
            k = self.select_helper(k, val, pos, depth + 1);
            rsbv.select1(k - zeros)
        } else {
            pos = rsbv.rank0(pos);
            k = self.select_helper(k, val, pos, depth + 1);
            rsbv.select0(k)
        }
    }

    /// Gets `k`-th smallest value in the given `range`.
    ///
    /// # Arguments
    ///
    /// - `range`: Position range to be searched.
    /// - `k`: Integer to be searched (`k >= 0`).
    ///
    /// # Complexity
    ///
    /// - $`O(\log \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::WaveletMatrix;
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_ints(text.chars().map(|c| c as usize)).unwrap();
    ///
    /// assert_eq!(wm.quantile(0..5, 0), 'b' as usize); // The zero-th in "tobeo" should be "b"
    /// assert_eq!(wm.quantile(0..5, 1), 'e' as usize); // The first in "tobeo" should be "e"
    /// assert_eq!(wm.quantile(0..5, 2), 'o' as usize); // The second in "tobeo" should be "o"
    /// assert_eq!(wm.quantile(0..5, 3), 'o' as usize); // The third in "tobeo" should be "o"
    /// assert_eq!(wm.quantile(0..5, 4), 't' as usize); // The fourth in "tobeo" should be "t"
    /// ```
    #[inline]
    pub fn quantile(&self, range: Range<usize>, mut k: usize) -> usize {
        assert!(k <= range.len(), "k must be less than range.len().");

        let mut val = 0;
        let mut start_pos = range.start;
        let mut end_pos = range.end;
        for depth in 0..self.width {
            val <<= 1;
            let rsbv = &self.layers[depth];
            let zero_start_pos = rsbv.rank0(start_pos);
            let zero_end_pos = rsbv.rank0(end_pos);
            let zeros = zero_end_pos - zero_start_pos;
            if k < zeros {
                start_pos = zero_start_pos;
                end_pos = zero_end_pos;
            } else {
                k -= zeros;
                val |= 1;
                start_pos = rsbv.num_zeros() + start_pos - zero_start_pos;
                end_pos = rsbv.num_zeros() + end_pos - zero_end_pos;
            }
        }
        val
    }

    /// Gets the all integers co-occurred more than `k` times in given `ranges`.
    ///
    /// # Arguments
    ///
    /// - `ranges`: A set of ranges to be searched.
    /// - `k`: Occurrence threshold.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::WaveletMatrix;
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_ints(text.chars().map(|c| c as usize)).unwrap();
    ///
    /// assert_eq!(wm.intersect(&[0..3, 4..5, 10..12], 2), vec!['b' as usize, 'o' as usize]); // "tob", "o", "ob"
    /// assert_eq!(wm.intersect(&[0..3, 4..5, 10..12], 3), vec!['o' as usize]); // "tob", "o", "ob"
    /// assert_eq!(wm.intersect(&[0..2, 2..4, 14..16], 2), vec![]); // "to", "be", "ha"
    /// ```
    #[inline(always)]
    pub fn intersect(&self, ranges: &[Range<usize>], k: usize) -> Vec<usize> {
        self.intersect_helper(ranges, k, 0, 0)
    }

    #[inline]
    fn intersect_helper(
        &self,
        ranges: &[Range<usize>],
        k: usize,
        depth: usize,
        prefix: usize,
    ) -> Vec<usize> {
        if depth == self.width {
            return vec![prefix];
        }

        let rsbv = &self.layers[depth];
        let mut zero_ranges = vec![];
        let mut one_ranges = vec![];
        for range in ranges {
            let start_pos = range.start;
            let end_pos = range.end;
            let zero_start_pos = rsbv.rank0(start_pos);
            let zero_end_pos = rsbv.rank0(end_pos);
            let one_start_pos = rsbv.num_zeros() + start_pos - zero_start_pos;
            let one_end_pos = rsbv.num_zeros() + end_pos - zero_end_pos;
            if zero_end_pos - zero_start_pos > 0 {
                zero_ranges.push(zero_start_pos..zero_end_pos)
            }
            if one_end_pos - one_start_pos > 0 {
                one_ranges.push(one_start_pos..one_end_pos)
            }
        }

        let mut ret = vec![];
        if zero_ranges.len() >= k {
            ret.extend_from_slice(&self.intersect_helper(&zero_ranges, k, depth + 1, prefix << 1));
        }
        if one_ranges.len() >= k {
            ret.extend_from_slice(&self.intersect_helper(
                &one_ranges,
                k,
                depth + 1,
                (prefix << 1) | 1,
            ));
        }
        ret
    }

    #[inline(always)]
    const fn get_msb(val: usize, pos: usize, width: usize) -> bool {
        ((val >> (width - pos - 1)) & 1) == 1
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::WaveletMatrix;
    ///
    /// let wm = WaveletMatrix::from_ints([20, 7, 13, 2]).unwrap();
    /// let mut it = wm.iter();
    ///
    /// assert_eq!(it.next(), Some(20));
    /// assert_eq!(it.next(), Some(7));
    /// assert_eq!(it.next(), Some(13));
    /// assert_eq!(it.next(), Some(2));
    /// assert_eq!(it.next(), None);
    /// ```
    pub const fn iter(&self) -> Iter {
        Iter::new(self)
    }
}

impl Searial for WaveletMatrix {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        writer.write_u64::<LittleEndian>(self.layers.len() as u64)?;
        for layer in &self.layers {
            mem += layer.serialize_into(&mut writer)?;
        }
        writer.write_u64::<LittleEndian>(self.dim as u64)?;
        writer.write_u64::<LittleEndian>(self.len as u64)?;
        writer.write_u64::<LittleEndian>(self.width as u64)?;
        Ok(mem + size_of::<u64>() * 4)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let layers = {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut layers = Vec::with_capacity(len);
            for _ in 0..len {
                layers.push(RsBitVector::deserialize_from(&mut reader)?);
            }
            layers
        };
        let dim = reader.read_u64::<LittleEndian>()? as usize;
        let len = reader.read_u64::<LittleEndian>()? as usize;
        let width = reader.read_u64::<LittleEndian>()? as usize;
        Ok(Self {
            layers,
            dim,
            len,
            width,
        })
    }

    fn size_in_bytes(&self) -> usize {
        let mut mem = 0;
        for layer in &self.layers {
            mem += layer.size_in_bytes();
        }
        mem + size_of::<u64>() * 4
    }
}

/// Builder of [`WaveletMatrix`].
pub struct WaveletMatrixBuilder {
    vals: Vec<usize>,
}

impl WaveletMatrixBuilder {
    /// Creates a new [`WaveletMatrixBuilder`].
    pub const fn new() -> Self {
        Self { vals: vec![] }
    }

    /// Pusheds integer `val` at the end
    ///
    /// # Arguments
    ///
    /// - `val` : Integer to be pushed.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let text = "tobeornottobethatisthequestion";
    /// text.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.len(), text.chars().count());
    /// assert_eq!(wm.dim(), ('u' as usize) + 1);
    ///
    /// assert_eq!(wm.get(20), 'h' as usize);
    /// assert_eq!(wm.rank(22, 'o' as usize), 4);
    /// assert_eq!(wm.select(2, 't' as usize), 9);
    /// ```
    pub fn push(&mut self, val: usize) {
        self.vals.push(val);
    }

    /// Builds [`WaveletMatrix`] from a sequence of pushed integers.
    ///
    /// # Errors
    ///
    /// `anyhow::Error` will be returned if `self.vals` is empty
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let text = "tobeornottobethatisthequestion";
    /// text.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.len(), text.chars().count());
    /// assert_eq!(wm.dim(), ('u' as usize) + 1);
    ///
    /// assert_eq!(wm.get(20), 'h' as usize);
    /// assert_eq!(wm.rank(22, 'o' as usize), 4);
    /// assert_eq!(wm.select(2, 't' as usize), 9);
    /// ```
    pub fn build(self) -> Result<WaveletMatrix> {
        if self.vals.is_empty() {
            return Err(anyhow!("vals must not be empty"));
        }

        let len = self.vals.len();
        let dim = self.get_dim();
        let width = Self::get_width(dim);

        let mut zeros = self.vals;
        let mut ones = vec![];
        let mut layers = vec![];

        for depth in 0..width {
            let mut next_zeros = Vec::with_capacity(len);
            let mut next_ones = Vec::with_capacity(len);
            let mut bv = BitVector::new();
            Self::filter(
                &zeros,
                width - depth - 1,
                &mut next_zeros,
                &mut next_ones,
                &mut bv,
            );
            Self::filter(
                &ones,
                width - depth - 1,
                &mut next_zeros,
                &mut next_ones,
                &mut bv,
            );
            zeros = next_zeros;
            ones = next_ones;
            layers.push(RsBitVector::new(bv).select1_hints().select0_hints());
        }

        Ok(WaveletMatrix {
            layers,
            dim,
            len,
            width,
        })
    }

    fn filter(
        vals: &[usize],
        shift: usize,
        next_zeros: &mut Vec<usize>,
        next_ones: &mut Vec<usize>,
        bv: &mut BitVector,
    ) {
        for &val in vals {
            let bit = ((val >> shift) & 1) == 1;
            bv.push_bit(bit);
            if bit {
                next_ones.push(val);
            } else {
                next_zeros.push(val);
            }
        }
    }

    fn get_dim(&self) -> usize {
        *self.vals.iter().max().unwrap() + 1
    }

    fn get_width(val: usize) -> usize {
        broadword::msb(val).unwrap() + 1
    }
}

impl Default for WaveletMatrixBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaChaRng;

    const SIGMA: usize = 256;

    fn gen_random_ints(len: usize, seed: u64) -> Vec<usize> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        (0..len).map(|_| rng.gen_range(0..SIGMA)).collect()
    }

    fn gen_random_ranges(len: usize, end: usize, seed: u64) -> Vec<Range<usize>> {
        let mut rng = ChaChaRng::seed_from_u64(seed);
        let mut ranges = vec![];
        for _ in 0..len {
            let i = rng.gen_range(0..end);
            let j = rng.gen_range(i..end);
            ranges.push(i..j);
        }
        ranges
    }

    fn test_lookup(ints: &[usize], wm: &WaveletMatrix) {
        for (i, &v) in ints.iter().enumerate() {
            assert_eq!(v, wm.get(i));
        }
    }

    fn test_iter(ints: &[usize], wm: &WaveletMatrix) {
        for (i, x) in wm.iter().enumerate() {
            assert_eq!(ints[i], x);
        }
    }

    fn test_rank_select(ints: &[usize], wm: &WaveletMatrix, val: usize) {
        let mut cur_rank = 0;
        for i in 0..ints.len() {
            assert_eq!(cur_rank, wm.rank(i, val));
            if ints[i] == val {
                assert_eq!(i, wm.select(cur_rank, val));
                cur_rank += 1;
            }
        }
    }

    fn test_rank_range(ints: &[usize], wm: &WaveletMatrix, ranges: &[Range<usize>], val: usize) {
        for rng in ranges {
            let (i, j) = (rng.start, rng.end);
            let expected = ints[i..j].iter().filter(|&&x| x == val).count();
            assert_eq!(expected, wm.rank_range(i..j, val));
        }
    }

    fn test_quantile(ints: &[usize], wm: &WaveletMatrix, ranges: &[Range<usize>]) {
        for rng in ranges {
            let (i, j) = (rng.start, rng.end);
            let mut tgt = ints[i..j].to_vec();
            for k in 0..rng.len() {
                let min_i = {
                    let exp = tgt.iter().enumerate().min_by_key(|&(_, x)| x).unwrap();
                    assert_eq!(*exp.1, wm.quantile(i..j, k));
                    exp.0
                };
                tgt.remove(min_i);
            }
        }
    }

    fn test_intersect(ints: &[usize], wm: &WaveletMatrix, ranges: &[Range<usize>]) {
        let mut sets = vec![];
        for rng in ranges {
            let mut set = std::collections::BTreeSet::new();
            ints[rng.start..rng.end].iter().for_each(|&x| {
                set.insert(x);
            });
            sets.push(set);
        }

        const K: usize = 1;

        for i in 0..ranges.len() - 3 {
            let q_rngs = &ranges[i..i + 3];
            let q_sets = &sets[i..i + 3];
            let expected = {
                let mut expected = std::collections::BTreeSet::new();
                for c in 0..SIGMA {
                    let mut cnt = 0;
                    for qs in q_sets {
                        if qs.contains(&c) {
                            cnt += 1;
                        }
                    }
                    if cnt >= K {
                        expected.insert(c);
                    }
                }
                expected
            };
            let answer = {
                let mut answer = std::collections::BTreeSet::new();
                for x in wm.intersect(q_rngs, K) {
                    answer.insert(x);
                }
                answer
            };
            assert_eq!(expected, answer);
        }
    }

    #[test]
    fn test_builder_push() {
        let mut wmb = WaveletMatrixBuilder::new();
        wmb.push(123);
        assert_eq!(wmb.get_dim(), 124);
    }

    #[test]
    fn test_builder_multi_push() {
        let mut wmb = WaveletMatrixBuilder::new();
        wmb.push(123);
        wmb.push(7777);
        wmb.push(987);
        assert_eq!(wmb.get_dim(), 7778);
    }

    #[test]
    #[should_panic]
    fn test_builder_with_emtpy_vals() {
        let wmb = WaveletMatrixBuilder::new();
        wmb.build().unwrap();
    }

    #[test]
    fn test_build() {
        /*
        This test example is from G. Navarro's "Compact Data Structures" P130
        */
        let text = "tobeornottobethatisthequestion";
        let len = text.chars().count();

        let wm = WaveletMatrix::from_ints(text.chars().map(|c| c as usize)).unwrap();
        assert_eq!(wm.len(), len);
        assert_eq!(wm.dim(), ('u' as usize) + 1);

        assert_eq!(wm.get(20), 'h' as usize);
        assert_eq!(wm.rank(22, 'o' as usize), 4);
        assert_eq!(wm.select(2, 't' as usize), 9);

        assert_eq!(wm.quantile(0..len, 0), 'a' as usize); // min
        assert_eq!(wm.quantile(0..len, len / 2), 'o' as usize); // median
        assert_eq!(wm.quantile(0..len, len - 1), 'u' as usize); // max
        assert_eq!(wm.quantile(0..3, 0), 'b' as usize); // zero-th in "tob" should be "b"

        let ranges = vec![0..3, 3..6];
        assert_eq!(wm.intersect(&ranges, 2), vec!['o' as usize])
    }

    #[test]
    fn test_random_ints() {
        let ints = gen_random_ints(1000, 13);
        let ranges = gen_random_ranges(30, ints.len(), 13);

        let wm = WaveletMatrix::from_ints(ints.iter().cloned()).unwrap();
        test_lookup(&ints, &wm);
        test_iter(&ints, &wm);
        for val in 0..SIGMA {
            test_rank_select(&ints, &wm, val);
            test_rank_range(&ints, &wm, &ranges, val);
        }
        test_quantile(&ints, &wm, &ranges);
        test_intersect(&ints, &wm, &ranges);
    }
}
