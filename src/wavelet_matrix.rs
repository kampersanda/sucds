use anyhow::{anyhow, Result};
use std::ops::Range;

use crate::{broadword, BitVector, RsBitVector};

/// Time- and space-efficient data structures for a sequence of integers,
/// supporting some queries such as ranking, selection, and intersection.
///
/// [`WaveletMatrix`] stores a sequence of integers and provides myriad operations on the sequence.
/// When a sequence stores $`n`$ integers from $`[0, \sigma -1]`$,
/// most of the operations run in $`O(log \sigma)`$ , using  $`n log \sigma + o (n log \sigma ) + O(log \sigma log n)`$ bits.
///
/// This is a yet another Rust port of [hillbig's waveletMatrix](https://github.com/hillbig/waveletTree/blob/master/waveletMatrix.go).
///
/// # Examples
///
/// ```
/// use sucds::{WaveletMatrix};
///
/// let text = "tobeornottobethatisthequestion";
/// let wm = WaveletMatrix::from_text(text).unwrap();
///
/// assert_eq!(wm.len(), text.chars().count());
/// assert_eq!(wm.dim(), 'u' as usize + 1);
///
/// assert_eq!(wm.lookup(20), 'h' as usize);
/// assert_eq!(wm.rank(22, 'o' as usize), 4);
/// assert_eq!(wm.select(2, 't' as usize), 9);
/// ```
///
/// # References
///
/// - F. Claude, and G. Navarro, "The Wavelet Matrix," In SPIRE 2012.
#[derive(Default, Debug, PartialEq, Eq)]
pub struct WaveletMatrix {
    layers: Vec<RsBitVector>,
    dim: usize,
    len: usize,
    bit_length: usize,
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
    /// use sucds::{WaveletMatrix};
    ///
    /// let ints = vec![20, 7, 13, 2, 11];
    /// let wm = WaveletMatrix::from_ints(&ints).unwrap();
    ///
    /// assert_eq!(wm.lookup(2), 13);
    /// assert_eq!(wm.len(), ints.len());
    /// assert_eq!(wm.dim(), 21);
    /// ```
    pub fn from_ints<'a, I>(ints: I) -> Result<Self>
    where
        I: IntoIterator<Item = &'a usize>,
    {
        let mut wmb = WaveletMatrixBuilder::default();
        for &v in ints {
            wmb.push(v);
        }
        wmb.build()
    }

    /// Builds a [`WaveletMatrix`] from characters in a string.
    /// Note that this handles a sequence of `char`, not `u8`.
    ///
    /// # Arguments
    ///
    /// - `text`: String.
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{WaveletMatrix};
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_text(text).unwrap();
    ///
    /// assert_eq!(wm.lookup(20), 'h' as usize);
    /// assert_eq!(wm.len(), text.chars().count());
    /// assert_eq!(wm.dim(), 'u' as usize + 1);
    /// ```
    pub fn from_text<S>(text: S) -> Result<Self>
    where
        S: AsRef<str>,
    {
        let mut wmb = WaveletMatrixBuilder::default();
        for c in text.as_ref().chars() {
            wmb.push(c as usize);
        }
        wmb.build()
    }

    /// Gets the maximum value + 1 in stored integers.
    pub const fn dim(&self) -> usize {
        self.dim
    }

    /// Gets the number of intergers stored in the `WaveletMatrix`.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Checks if the list of intergers is empty.
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the maximum numbber of bits needed to be stored for each integers.
    pub const fn bit_length(&self) -> usize {
        self.bit_length
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
    /// use sucds::{WaveletMatrix};
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_text(text).unwrap();
    ///
    /// assert_eq!(wm.lookup(20), 'h' as usize);
    /// ```
    pub fn lookup(&self, mut pos: usize) -> usize {
        let mut val = 0;
        for depth in 0..self.bit_length as usize {
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
    /// use sucds::{WaveletMatrix};
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_text(text).unwrap();
    ///
    /// assert_eq!(wm.rank(22, 'o' as usize), 4);
    /// ```
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
    /// use sucds::{WaveletMatrix};
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_text(text).unwrap();
    ///
    /// assert_eq!(wm.rank_range(0..22, 'o' as usize), 4);
    /// ```
    pub fn rank_range(&self, range: Range<usize>, val: usize) -> usize {
        let mut start_pos = range.start;
        let mut end_pos = range.end;
        for depth in 0..self.bit_length as usize {
            let bit = Self::get_msb(val, depth, self.bit_length);
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

    /// Gets the occurrence position of `rank`-th `val` in [0, n).
    ///
    /// # Arguments
    ///
    /// - `rank`: Rank to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{WaveletMatrix};
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_text(text).unwrap();
    ///
    /// assert_eq!(wm.select(2, 't' as usize), 9);
    /// ```
    pub fn select(&self, rank: usize, val: usize) -> usize {
        self.select_helper(rank, val, 0, 0)
    }

    fn select_helper(&self, mut rank: usize, val: usize, mut pos: usize, depth: usize) -> usize {
        if depth == self.bit_length {
            return pos + rank;
        }
        let bit = Self::get_msb(val, depth, self.bit_length);
        let rsbv = &self.layers[depth];
        if bit {
            let zeros = rsbv.num_zeros();
            pos = rsbv.rank1(pos) + zeros;
            rank = self.select_helper(rank, val, pos, depth + 1);
            rsbv.select1(rank - zeros)
        } else {
            pos = rsbv.rank0(pos);
            rank = self.select_helper(rank, val, pos, depth + 1);
            rsbv.select0(rank)
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
    /// use sucds::{WaveletMatrix};
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_text(text).unwrap();
    ///
    /// assert_eq!(wm.quantile(0..5, 0), 'b' as usize); // The zero-th in "tobeo" should be "b"
    /// assert_eq!(wm.quantile(0..5, 1), 'e' as usize); // The first in "tobeo" should be "e"
    /// assert_eq!(wm.quantile(0..5, 2), 'o' as usize); // The second in "tobeo" should be "o"
    /// assert_eq!(wm.quantile(0..5, 3), 'o' as usize); // The third in "tobeo" should be "o"
    /// assert_eq!(wm.quantile(0..5, 4), 't' as usize); // The fourth in "tobeo" should be "t"
    /// ```
    pub fn quantile(&self, range: Range<usize>, mut k: usize) -> usize {
        assert!(k <= range.len(), "k must be less than range.len().");

        let mut val = 0;
        let mut start_pos = range.start;
        let mut end_pos = range.end;
        for depth in 0..self.bit_length {
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
    /// use sucds::{WaveletMatrix};
    ///
    /// let text = "tobeornottobethatisthequestion";
    /// let wm = WaveletMatrix::from_text(text).unwrap();
    ///
    /// assert_eq!(wm.intersect(&[0..3, 4..5, 10..12], 2), vec!['b' as usize, 'o' as usize]); // "tob", "o", "ob"
    /// assert_eq!(wm.intersect(&[0..3, 4..5, 10..12], 3), vec!['o' as usize]); // "tob", "o", "ob"
    /// assert_eq!(wm.intersect(&[0..2, 2..4, 14..16], 2), vec![]); // "to", "be", "ha"
    /// ```
    pub fn intersect(&self, ranges: &[Range<usize>], k: usize) -> Vec<usize> {
        self.intersect_helper(ranges, k, 0, 0)
    }

    fn intersect_helper(
        &self,
        ranges: &[Range<usize>],
        k: usize,
        depth: usize,
        prefix: usize,
    ) -> Vec<usize> {
        if depth == self.bit_length {
            return vec![prefix];
        }

        let rsbv = &self.layers[depth];
        let mut zero_ranges = Vec::new();
        let mut one_ranges = Vec::new();
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

        let mut ret = Vec::new();
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

    const fn get_msb(val: usize, pos: usize, bit_length: usize) -> bool {
        ((val >> (bit_length - pos - 1)) & 1) == 1
    }
}

/// Builder of [`WaveletMatrix`].
pub struct WaveletMatrixBuilder {
    vals: Vec<usize>,
}

impl WaveletMatrixBuilder {
    /// Creates a new [`WaveletMatrixBuilder`].
    pub const fn new() -> Self {
        Self { vals: Vec::new() }
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
    /// assert_eq!(wm.lookup(20), 'h' as usize);
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
    /// assert_eq!(wm.lookup(20), 'h' as usize);
    /// assert_eq!(wm.rank(22, 'o' as usize), 4);
    /// assert_eq!(wm.select(2, 't' as usize), 9);
    /// ```
    pub fn build(&self) -> Result<WaveletMatrix> {
        if self.vals.is_empty() {
            return Err(anyhow!("vals must not be empty"));
        }

        let dim = self.get_dim()?;
        let bit_length = Self::get_bit_length(dim)?;
        let mut zeros: Vec<usize> = self.vals.clone();
        let mut ones: Vec<usize> = Vec::new();
        let mut layers: Vec<RsBitVector> = Vec::new();
        for depth in 0..bit_length {
            let mut next_zeros: Vec<usize> = Vec::with_capacity(self.vals.len());
            let mut next_ones: Vec<usize> = Vec::with_capacity(self.vals.len());
            let mut bv = BitVector::new();
            Self::filter(
                &zeros,
                bit_length - depth - 1,
                &mut next_zeros,
                &mut next_ones,
                &mut bv,
            );
            Self::filter(
                &ones,
                bit_length - depth - 1,
                &mut next_zeros,
                &mut next_ones,
                &mut bv,
            );
            zeros = next_zeros;
            ones = next_ones;
            layers.push(RsBitVector::new(bv, true, true));
        }
        Ok(WaveletMatrix {
            layers,
            dim,
            len: self.vals.len(),
            bit_length,
        })
    }

    fn filter(
        vals: &[usize],
        shift: usize,
        next_zeros: &mut Vec<usize>,
        next_ones: &mut Vec<usize>,
        bv: &mut BitVector,
    ) {
        for val in vals {
            let bit = ((*val >> shift) & 1) == 1;
            bv.push_bit(bit);
            if bit {
                next_ones.push(*val);
            } else {
                next_zeros.push(*val);
            }
        }
    }

    fn get_dim(&self) -> Result<usize> {
        match self.vals.iter().max() {
            Some(i) => Ok(*i + 1),
            None => Err(anyhow!("cannot extract max value")),
        }
    }

    fn get_bit_length(val: usize) -> Result<usize> {
        match broadword::msb(val) {
            Some(i) => Ok(i + 1),
            None => Err(anyhow!("cannot calculate msb")),
        }
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
            assert_eq!(v, wm.lookup(i));
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
        assert_eq!(wmb.get_dim().unwrap(), 124);
    }

    #[test]
    fn test_builder_multi_push() {
        let mut wmb = WaveletMatrixBuilder::new();
        wmb.push(123);
        wmb.push(7777);
        wmb.push(987);
        assert_eq!(wmb.get_dim().unwrap(), 7778);
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

        let wm = WaveletMatrix::from_text(text).unwrap();
        assert_eq!(wm.len(), len);
        assert_eq!(wm.dim(), ('u' as usize) + 1);

        assert_eq!(wm.lookup(20), 'h' as usize);
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

        let wm = WaveletMatrix::from_ints(&ints).unwrap();
        test_lookup(&ints, &wm);
        for val in 0..SIGMA {
            test_rank_select(&ints, &wm, val);
            test_rank_range(&ints, &wm, &ranges, val);
        }
        test_quantile(&ints, &wm, &ranges);
        test_intersect(&ints, &wm, &ranges);
    }
}
