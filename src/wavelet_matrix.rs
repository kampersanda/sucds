use anyhow::{anyhow, Result};
use std::ops::Range;

use crate::{broadword, BitVector, RsBitVector};

/// Time and space efficient index data structures for sequence.
///
/// [`WaveletMatrix`] implements stores a sequence of integers and provides myriad operations on sequece.
/// When a sequence stores $`n`$ integers from $`[0, u-1]`$,
/// most of the operations run in $`O(log u)`$ , using  $`n log u + o (n log u) + O(log u log n)`$ bits.
///
/// This is a yet another Rust port of [hillbig's waveletMatrix](https://github.com/hillbig/waveletTree/blob/master/waveletMatrix.go).
///
/// # Example
///
/// ```
/// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
///
/// let mut wmb = WaveletMatrixBuilder::new();
/// let s = "tobeornottobethatisthequestion";
/// s.chars().for_each(|c| wmb.push(c as usize));
///
/// let wm = wmb.build().unwrap();
/// assert_eq!(wm.num(), s.len());
/// assert_eq!(wm.dim(), ('u' as usize) + 1);
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
    num: usize,
    bit_length: usize,
}

impl WaveletMatrix {
    /// Creates a new [`WaveletMatrix`].
    ///
    /// # Arguments
    ///
    /// - `layers`: A sequence of `RsBitVector`.
    /// - `dim`:
    /// - `num`: The number of integers to be stored
    /// - `bit_length `:
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let s = "tobeornottobethatisthequestion";
    /// s.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.num(), s.len());
    /// assert_eq!(wm.dim(), ('u' as usize) + 1);
    ///
    /// assert_eq!(wm.lookup(20), 'h' as usize);
    /// assert_eq!(wm.rank(22, 'o' as usize), 4);
    /// assert_eq!(wm.select(2, 't' as usize), 9);
    /// ```
    pub fn new(layers: Vec<RsBitVector>, dim: usize, num: usize, bit_length: usize) -> Self {
        Self {
            layers,
            dim,
            num,
            bit_length,
        }
    }

    /// Gets the maximum value + 1 in stored integers.
    pub fn dim(&self) -> usize {
        self.dim
    }

    /// Gets the number of intergers stored in the `WaveletMatrix`.
    pub fn num(&self) -> usize {
        self.num
    }

    /// Gets the maximum numbber of bits needed to be stored for each integers.
    pub fn bit_length(&self) -> usize {
        self.bit_length
    }

    /// Gets the integer located in `pos`.
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
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let s = "tobeornottobethatisthequestion";
    /// s.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.lookup(20), 'h' as usize);
    /// ```
    pub fn lookup(&self, pos: usize) -> usize {
        let mut val = 0;
        let mut pos = pos;
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
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let s = "tobeornottobethatisthequestion";
    /// s.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.rank(22, 'o' as usize), 4);
    /// ```
    pub fn rank(&self, pos: usize, val: usize) -> usize {
        let range = self.rank_range(Range { start: 0, end: pos }, val);
        range.len()
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
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let s = "tobeornottobethatisthequestion";
    /// s.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.rank_rank(Range{start: 0, end: 22}, 'o' as usize), 4);
    /// ```
    pub fn rank_range(&self, range: Range<usize>, val: usize) -> Range<usize> {
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
        Range {
            start: start_pos,
            end: end_pos,
        }
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
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let s = "tobeornottobethatisthequestion";
    /// s.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.select(2, 't' as usize), 9);
    /// ```
    pub fn select(&self, rank: usize, val: usize) -> usize {
        self.select_helper(rank, val, 0, 0)
    }

    fn select_helper(&self, rank: usize, val: usize, pos: usize, depth: usize) -> usize {
        if depth == self.bit_length {
            return pos + rank;
        }
        let mut pos = pos;
        let mut rank = rank;
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

    /// Gets `k+1`-th smallest value in the given `range`.
    ///
    /// # Arguments
    ///
    /// - `range`: Position to be searched.
    /// - `k`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// - $`O(\log \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let s = "tobeornottobethatisthequestion";
    /// s.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.quantile(Range { start: 0, end: 3 }, 0), 'b' as usize); // min in "tob" should be "b"
    /// ```
    pub fn quantile(&self, range: Range<usize>, k: usize) -> usize {
        let mut val = 0;
        let mut start_pos = range.start;
        let mut end_pos = range.end;
        let mut k = k;
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
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let s = "tobeornottobethatisthequestion";
    /// s.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// let ranges = vec![Range { start: 0, end: 3 }, Range { start: 3, end: 6 }];
    /// assert_eq!(wm.intersect(ranges, 2), vec!['o' as usize]);
    /// ```
    pub fn intersect(&self, ranges: Vec<Range<usize>>, k: usize) -> Vec<usize> {
        self.intersect_helper(ranges, k, 0, 0)
    }

    fn intersect_helper(
        &self,
        ranges: Vec<Range<usize>>,
        k: usize,
        depth: usize,
        prefix: usize,
    ) -> Vec<usize> {
        if depth == self.bit_length {
            let ret = vec![prefix];
            return ret;
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
                zero_ranges.push(Range {
                    start: zero_start_pos,
                    end: zero_end_pos,
                })
            }
            if one_end_pos - one_start_pos > 0 {
                one_ranges.push(Range {
                    start: one_start_pos,
                    end: one_end_pos,
                })
            }
        }

        let mut ret = Vec::new();
        if zero_ranges.len() >= k {
            ret.extend_from_slice(&self.intersect_helper(zero_ranges, k, depth + 1, prefix << 1));
        }
        if one_ranges.len() >= k {
            ret.extend_from_slice(&self.intersect_helper(
                one_ranges,
                k,
                depth + 1,
                (prefix << 1) | 1,
            ));
        }
        ret
    }

    fn get_msb(val: usize, pos: usize, bit_length: usize) -> bool {
        ((val >> (bit_length - pos - 1)) & 1) == 1
    }
}

pub struct WaveletMatrixBuilder {
    vals: Vec<usize>,
}

impl WaveletMatrixBuilder {
    /// Creates a new [`WaveletMatrixBuilder`].
    pub fn new() -> Self {
        WaveletMatrixBuilder { vals: Vec::new() }
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
    /// let s = "tobeornottobethatisthequestion";
    /// s.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.num(), s.len());
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
    /// `anyhow:: Error` will be returned if `self.vals` is empty
    ///
    /// # Examples
    ///
    /// ```
    /// use sucds::{WaveletMatrix, WaveletMatrixBuilder};
    ///
    /// let mut wmb = WaveletMatrixBuilder::new();
    /// let s = "tobeornottobethatisthequestion";
    /// s.chars().for_each(|c| wmb.push(c as usize));
    ///
    /// let wm = wmb.build().unwrap();
    /// assert_eq!(wm.num(), s.len());
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
        Ok(WaveletMatrix::new(layers, dim, self.vals.len(), bit_length))
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
        let mut wmb = WaveletMatrixBuilder::new();
        let s = "tobeornottobethatisthequestion";
        s.chars().for_each(|c| wmb.push(c as usize));

        let wm = wmb.build().unwrap();
        assert_eq!(wm.num(), s.len());
        assert_eq!(wm.dim(), ('u' as usize) + 1);

        assert_eq!(wm.lookup(20), 'h' as usize);
        assert_eq!(wm.rank(22, 'o' as usize), 4);
        assert_eq!(wm.select(2, 't' as usize), 9);

        assert_eq!(
            wm.quantile(
                Range {
                    start: 0,
                    end: s.len()
                },
                0
            ),
            'a' as usize
        ); // min

        assert_eq!(
            wm.quantile(
                Range {
                    start: 0,
                    end: s.len()
                },
                s.len() / 2
            ),
            'o' as usize
        ); // median

        assert_eq!(
            wm.quantile(
                Range {
                    start: 0,
                    end: s.len()
                },
                s.len() - 1
            ),
            'u' as usize
        ); // max

        assert_eq!(wm.quantile(Range { start: 0, end: 3 }, 0), 'b' as usize); // min in "tob" should be "b"

        let ranges = vec![Range { start: 0, end: 3 }, Range { start: 3, end: 6 }];
        assert_eq!(wm.intersect(ranges, 2), vec!['o' as usize])
    }
}
