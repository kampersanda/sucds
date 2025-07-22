//! Time- and space-efficient data structure for a sequence of integers,
//! supporting some queries such as ranking, selection, and intersection.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};
use std::ops::Range;

use anyhow::{anyhow, Result};

use crate::bit_vectors::{Access, BitVector, Build, NumBits, Rank, Select};
use crate::int_vectors::CompactVector;
use crate::utils;
use crate::Serializable;

/// Time- and space-efficient data structure for a sequence of integers,
/// supporting some queries such as ranking, selection, and intersection.
///
/// [`WaveletMatrix`] stores a sequence of integers and provides myriad operations on the sequence.
/// When a sequence stores $`n`$ integers from $`[0, \sigma)`$,
/// most of the operations run in $`O(\lg \sigma)`$ time, using  $`O(n \lg \sigma )`$ bits of memory
/// (assuming bit vectors in constant-time and linear-space).
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use sucds::bit_vectors::Rank9Sel;
/// use sucds::char_sequences::WaveletMatrix;
/// use sucds::int_vectors::CompactVector;
///
/// let text = "banana";
/// let len = text.chars().count();
///
/// // It accepts an integer representable in 8 bits.
/// let mut seq = CompactVector::new(8)?;
/// seq.extend(text.chars().map(|c| c as usize))?;
/// let wm = WaveletMatrix::<Rank9Sel>::new(seq)?;
///
/// assert_eq!(wm.len(), len);
/// assert_eq!(wm.alph_size(), 'n' as usize + 1);
/// assert_eq!(wm.alph_width(), 7);
///
/// assert_eq!(wm.access(2), Some('n' as usize ));
/// assert_eq!(wm.rank(3, 'a' as usize), Some(1));
/// assert_eq!(wm.select(1, 'n' as usize), Some(4));
/// # Ok(())
/// # }
/// ```
///
/// # Credits
///
/// This is a yet another Rust port of [hillbig's waveletMatrix](https://github.com/hillbig/waveletTree/blob/master/waveletMatrix.go).
///
/// # References
///
/// - F. Claude, and G. Navarro, "The Wavelet Matrix," In SPIRE 2012.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct WaveletMatrix<B> {
    layers: Vec<B>,
    alph_size: u64,
}

impl<B> WaveletMatrix<B>
where
    B: Access + Build + NumBits + Rank + Select,
{
    /// Creates a new instance from an input sequence `seq`.
    ///
    /// # Errors
    ///
    /// An error is returned if
    ///
    ///  - `seq` is empty, or
    ///  - `B::build_from_bits` fails.
    pub fn new(seq: CompactVector) -> Result<Self> {
        if seq.is_empty() {
            return Err(anyhow!("seq must not be empty."));
        }

        let alph_size = seq.iter().max().unwrap() + 1;
        let alph_width = utils::needed_bits(alph_size);

        let mut zeros = seq;
        let mut ones = CompactVector::new(alph_width).unwrap();
        let mut layers = vec![];

        for depth in 0..alph_width {
            let mut next_zeros = CompactVector::new(alph_width).unwrap();
            let mut next_ones = CompactVector::new(alph_width).unwrap();
            let mut bv = BitVector::new();
            Self::filter(
                &zeros,
                alph_width - depth - 1,
                &mut next_zeros,
                &mut next_ones,
                &mut bv,
            );
            Self::filter(
                &ones,
                alph_width - depth - 1,
                &mut next_zeros,
                &mut next_ones,
                &mut bv,
            );
            zeros = next_zeros;
            ones = next_ones;
            layers.push(B::build_from_bits(bv.iter(), true, true, true)?);
        }

        Ok(Self { layers, alph_size })
    }

    fn filter(
        seq: &CompactVector,
        shift: usize,
        next_zeros: &mut CompactVector,
        next_ones: &mut CompactVector,
        bv: &mut BitVector,
    ) {
        for val in seq.iter() {
            let bit = ((val >> shift) & 1) == 1;
            bv.push_bit(bit);
            if bit {
                next_ones.push_int(val).unwrap();
            } else {
                next_zeros.push_int(val).unwrap();
            }
        }
    }

    /// Returns the `pos`-th integer, or [`None`] if `self.len() <= pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position to access.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::Rank9Sel;
    /// use sucds::char_sequences::WaveletMatrix;
    /// use sucds::int_vectors::CompactVector;
    ///
    /// let mut seq = CompactVector::new(8)?;
    /// seq.extend("banana".chars().map(|c| c as usize))?;
    /// let wm = WaveletMatrix::<Rank9Sel>::new(seq)?;
    ///
    /// assert_eq!(wm.access(2), Some('n' as usize));
    /// assert_eq!(wm.access(5), Some('a' as usize));
    /// assert_eq!(wm.access(6), None);
    /// # Ok(())
    /// # }
    /// ```
    // NOTE(kampersanda): We should not use `get()` because it has been already used in most std
    // containers with different type annotations.
    #[inline(always)]
    pub fn access(&self, mut pos: usize) -> Option<usize> {
        if self.len() <= pos {
            return None;
        }
        let mut val = 0;
        for layer in &self.layers {
            val <<= 1;
            if layer.access(pos).unwrap() {
                val |= 1;
                pos = layer.rank1(pos).unwrap() + layer.num_zeros();
            } else {
                pos = layer.rank0(pos).unwrap();
            }
        }
        Some(val)
    }

    /// Returns the number of occurrence of `val` in the range `0..pos`,
    /// or [`None`] if `self.len() < pos`.
    ///
    /// # Arguments
    ///
    /// - `pos`: Position to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::Rank9Sel;
    /// use sucds::char_sequences::WaveletMatrix;
    /// use sucds::int_vectors::CompactVector;
    ///
    /// let mut seq = CompactVector::new(8)?;
    /// seq.extend("banana".chars().map(|c| c as usize))?;
    /// let wm = WaveletMatrix::<Rank9Sel>::new(seq)?;
    ///
    /// assert_eq!(wm.rank(3, 'a' as usize), Some(1));
    /// assert_eq!(wm.rank(5, 'c' as usize), Some(0));
    /// assert_eq!(wm.rank(7, 'b' as usize), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn rank(&self, pos: usize, val: usize) -> Option<usize> {
        self.rank_range(0..pos, val)
    }

    /// Returns the number of occurrence of `val` in the given `range`,
    /// or [`None`] if `range` is out of bounds.
    ///
    /// # Arguments
    ///
    /// - `range`: Position range to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::Rank9Sel;
    /// use sucds::char_sequences::WaveletMatrix;
    /// use sucds::int_vectors::CompactVector;
    ///
    /// let mut seq = CompactVector::new(8)?;
    /// seq.extend("banana".chars().map(|c| c as usize))?;
    /// let wm = WaveletMatrix::<Rank9Sel>::new(seq)?;
    ///
    /// assert_eq!(wm.rank_range(1..4, 'a' as usize), Some(2));
    /// assert_eq!(wm.rank_range(2..4, 'c' as usize), Some(0));
    /// assert_eq!(wm.rank_range(4..7, 'b' as usize), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn rank_range(&self, range: Range<usize>, val: usize) -> Option<usize> {
        if range.is_empty() {
            return Some(0);
        }
        if self.len() < range.end {
            return None;
        }

        let mut start_pos = range.start;
        let mut end_pos = range.end;

        // NOTE(kampersanda): rank should be safe because of the precheck.
        for (depth, layer) in self.layers.iter().enumerate() {
            let bit = Self::get_msb(val, depth, self.alph_width());
            if bit {
                start_pos = layer.rank1(start_pos).unwrap() + layer.num_zeros();
                end_pos = layer.rank1(end_pos).unwrap() + layer.num_zeros();
            } else {
                start_pos = layer.rank0(start_pos).unwrap();
                end_pos = layer.rank0(end_pos).unwrap();
            }
        }
        Some((start_pos..end_pos).len())
    }

    /// Returns the occurrence position of `k`-th `val`,
    /// or [`None`] if there is no such an occurrence.
    ///
    /// # Arguments
    ///
    /// - `k`: Rank to be searched.
    /// - `val`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::Rank9Sel;
    /// use sucds::char_sequences::WaveletMatrix;
    /// use sucds::int_vectors::CompactVector;
    ///
    /// let mut seq = CompactVector::new(8)?;
    /// seq.extend("banana".chars().map(|c| c as usize))?;
    /// let wm = WaveletMatrix::<Rank9Sel>::new(seq)?;
    ///
    /// assert_eq!(wm.select(1, 'a' as usize), Some(3));
    /// assert_eq!(wm.select(0, 'c' as usize), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn select(&self, k: usize, val: usize) -> Option<usize> {
        self.select_helper(k, val, 0, 0)
    }

    #[inline]
    fn select_helper(
        &self,
        mut k: usize,
        val: usize,
        mut pos: usize,
        depth: usize,
    ) -> Option<usize> {
        if depth == self.alph_width() {
            return Some(pos + k);
        }
        let bit = Self::get_msb(val, depth, self.alph_width());
        let layer = &self.layers[depth];
        if bit {
            let zeros = layer.num_zeros();
            // NOTE(kampersanda): rank should be safe.
            pos = layer.rank1(pos).unwrap() + zeros;
            k = self.select_helper(k, val, pos, depth + 1)?;
            layer.select1(k - zeros)
        } else {
            // NOTE(kampersanda): rank should be safe.
            pos = layer.rank0(pos).unwrap();
            k = self.select_helper(k, val, pos, depth + 1)?;
            layer.select0(k)
        }
    }

    /// Returns `k`-th smallest value in the given `range`,
    /// or [`None`] if `range.len() <= k` or `range` is out of bounds.
    ///
    /// # Arguments
    ///
    /// - `range`: Position range to be searched.
    /// - `k`: Integer to be searched.
    ///
    /// # Complexity
    ///
    /// $`O(\lg \sigma)`$
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::Rank9Sel;
    /// use sucds::char_sequences::WaveletMatrix;
    /// use sucds::int_vectors::CompactVector;
    ///
    /// let mut seq = CompactVector::new(8)?;
    /// seq.extend("banana".chars().map(|c| c as usize))?;
    /// let wm = WaveletMatrix::<Rank9Sel>::new(seq)?;
    ///
    /// assert_eq!(wm.quantile(1..4, 0), Some('a' as usize)); // The 0th in "ana" should be "a"
    /// assert_eq!(wm.quantile(1..4, 1), Some('a' as usize)); // The 1st in "ana" should be "a"
    /// assert_eq!(wm.quantile(1..4, 2), Some('n' as usize)); // The 1st in "ana" should be "n"
    /// assert_eq!(wm.quantile(1..4, 3), None);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn quantile(&self, range: Range<usize>, mut k: usize) -> Option<usize> {
        if range.len() <= k {
            return None;
        }
        if self.len() < range.end {
            return None;
        }

        let mut val = 0;
        let mut start_pos = range.start;
        let mut end_pos = range.end;

        for layer in &self.layers {
            val <<= 1;
            // NOTE(kampersanda): rank should be safe because of the precheck.
            let zero_start_pos = layer.rank0(start_pos).unwrap();
            let zero_end_pos = layer.rank0(end_pos).unwrap();
            let zeros = zero_end_pos - zero_start_pos;
            if k < zeros {
                start_pos = zero_start_pos;
                end_pos = zero_end_pos;
            } else {
                k -= zeros;
                val |= 1;
                start_pos = layer.num_zeros() + start_pos - zero_start_pos;
                end_pos = layer.num_zeros() + end_pos - zero_end_pos;
            }
        }
        Some(val)
    }

    /// Returns the all integers co-occurred more than `k` times in given `ranges`,
    /// or [`None`] if any range in `ranges` is out of bounds.
    ///
    /// Note that `Some(vec![])`, not [`None`], will be returned if there is no occurrence.
    ///
    /// # Arguments
    ///
    /// - `ranges`: Ranges to be searched.
    /// - `k`: Occurrence threshold.
    ///
    /// # Complexity
    ///
    /// $`O( \min(\sigma, j_1 - i_1, \dots, j_r - i_r ) )`$ for `ranges` is $`[(i_1,j_1),\dots,(i_r,j_r)]`$.[^intersect]
    ///
    /// [^intersect]: A tighter bound is analyzed in the paper: Gagie, Travis, Gonzalo Navarro, and Simon J. Puglisi.
    /// "New algorithms on wavelet trees and applications to information retrieval." Theoretical Computer Science 426 (2012): 25-41.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::Rank9Sel;
    /// use sucds::char_sequences::WaveletMatrix;
    /// use sucds::int_vectors::CompactVector;
    ///
    /// let mut seq = CompactVector::new(8)?;
    /// seq.extend("banana".chars().map(|c| c as usize))?;
    /// let wm = WaveletMatrix::<Rank9Sel>::new(seq)?;
    ///
    /// // Intersections among "ana", "na", and "ba".
    /// assert_eq!(
    ///     wm.intersect(&[1..4, 4..6, 0..2], 0),
    ///     Some(vec!['a' as usize, 'b' as usize, 'n' as usize])
    /// );
    /// assert_eq!(
    ///     wm.intersect(&[1..4, 4..6, 0..2], 1),
    ///     Some(vec!['a' as usize, 'n' as usize])
    /// );
    /// assert_eq!(
    ///     wm.intersect(&[1..4, 4..6, 0..2], 2),
    ///     Some(vec!['a' as usize])
    /// );
    /// assert_eq!(
    ///     wm.intersect(&[1..4, 4..6, 0..2], 3),
    ///     Some(vec![])
    /// );
    /// # Ok(())
    /// # }
    /// ```
    #[inline(always)]
    pub fn intersect(&self, ranges: &[Range<usize>], k: usize) -> Option<Vec<usize>> {
        self.intersect_helper(ranges, k, 0, 0)
    }

    #[inline]
    fn intersect_helper(
        &self,
        ranges: &[Range<usize>],
        k: usize,
        depth: usize,
        prefix: usize,
    ) -> Option<Vec<usize>> {
        if depth == self.alph_width() {
            return Some(vec![prefix]);
        }

        let mut zero_ranges = vec![];
        let mut one_ranges = vec![];

        let layer = &self.layers[depth];
        for range in ranges {
            if layer.num_bits() < range.end {
                return None;
            }
            // NOTE(kampersanda): An empty range should be skipped because it is never co-occurred.
            if range.is_empty() {
                continue;
            }

            let start_pos = range.start;
            let end_pos = range.end;

            // NOTE(kampersanda): rank should be safe because of the precheck.
            let zero_start_pos = layer.rank0(start_pos).unwrap();
            let zero_end_pos = layer.rank0(end_pos).unwrap();
            let one_start_pos = layer.num_zeros() + start_pos - zero_start_pos;
            let one_end_pos = layer.num_zeros() + end_pos - zero_end_pos;

            if zero_end_pos - zero_start_pos > 0 {
                zero_ranges.push(zero_start_pos..zero_end_pos)
            }
            if one_end_pos - one_start_pos > 0 {
                one_ranges.push(one_start_pos..one_end_pos)
            }
        }

        let mut ret = vec![];
        if zero_ranges.len() > k {
            ret.extend_from_slice(&self.intersect_helper(
                &zero_ranges,
                k,
                depth + 1,
                prefix << 1,
            )?);
        }
        if one_ranges.len() > k {
            ret.extend_from_slice(&self.intersect_helper(
                &one_ranges,
                k,
                depth + 1,
                (prefix << 1) | 1,
            )?);
        }
        Some(ret)
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
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// use sucds::bit_vectors::Rank9Sel;
    /// use sucds::char_sequences::WaveletMatrix;
    /// use sucds::int_vectors::CompactVector;
    ///
    /// let mut seq = CompactVector::new(8)?;
    /// seq.extend("ban".chars().map(|c| c as usize))?;
    /// let wm = WaveletMatrix::<Rank9Sel>::new(seq)?;
    ///
    /// let mut it = wm.iter();
    /// assert_eq!(it.next(), Some('b' as usize));
    /// assert_eq!(it.next(), Some('a' as usize));
    /// assert_eq!(it.next(), Some('n' as usize));
    /// assert_eq!(it.next(), None);
    /// # Ok(())
    /// # }
    /// ```
    pub const fn iter(&self) -> Iter<B> {
        Iter::new(self)
    }

    /// Returns the number of values stored.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.layers.first().map(|l| l.num_bits()).unwrap_or(0)
    }

    /// Checks if the sequence is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the maximum value + 1 in the sequence, i.e., $`\sigma`$.
    #[inline(always)]
    pub const fn alph_size(&self) -> u64 {
        self.alph_size
    }

    /// Returns $`\lceil \log_2{\sigma} \rceil`$, which is the number of layers in the matrix.
    #[inline(always)]
    pub fn alph_width(&self) -> usize {
        self.layers.len()
    }
}

/// Iterator for enumerating integers, created by [`WaveletMatrix::iter()`].
pub struct Iter<'a, B> {
    wm: &'a WaveletMatrix<B>,
    pos: usize,
}

impl<'a, B> Iter<'a, B> {
    /// Creates a new iterator.
    pub const fn new(wm: &'a WaveletMatrix<B>) -> Self {
        Self { wm, pos: 0 }
    }
}

impl<B> Iterator for Iter<'_, B>
where
    B: Access + Build + NumBits + Rank + Select,
{
    type Item = usize;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        // TODO(kampersanda): Optimization with caching.
        if self.pos < self.wm.len() {
            let x = self.wm.access(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.wm.len(), Some(self.wm.len()))
    }
}

impl<B> Serializable for WaveletMatrix<B>
where
    B: Serializable,
{
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = self.layers.serialize_into(&mut writer)?;
        mem += self.alph_size.serialize_into(&mut writer)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let layers = Vec::<B>::deserialize_from(&mut reader)?;
        let alph_size = u64::deserialize_from(&mut reader)?;
        Ok(Self { layers, alph_size })
    }

    fn size_in_bytes(&self) -> usize {
        self.layers.size_in_bytes() + usize::size_of().unwrap()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::bit_vectors::Rank9Sel;

    #[test]
    fn test_empty_seq() {
        let e = WaveletMatrix::<Rank9Sel>::new(CompactVector::new(1).unwrap());
        assert_eq!(
            e.err().map(|x| x.to_string()),
            Some("seq must not be empty.".to_string())
        );
    }

    #[test]
    fn test_navarro_book() {
        // This test example is from G. Navarro's "Compact Data Structures" P130
        let text = "tobeornottobethatisthequestion";
        let len = text.chars().count();

        let mut seq = CompactVector::new(8).unwrap();
        seq.extend(text.chars().map(|c| c as usize)).unwrap();
        let wm = WaveletMatrix::<Rank9Sel>::new(seq).unwrap();

        assert_eq!(wm.len(), len);
        assert_eq!(wm.alph_size(), ('u' as usize) + 1);
        assert_eq!(wm.alph_width(), 7);

        assert_eq!(wm.access(20), Some('h' as usize));
        assert_eq!(wm.rank(22, 'o' as usize), Some(4));
        assert_eq!(wm.select(2, 't' as usize), Some(9));

        assert_eq!(wm.quantile(0..len, 0), Some('a' as usize)); // min
        assert_eq!(wm.quantile(0..len, len / 2), Some('o' as usize)); // median
        assert_eq!(wm.quantile(0..len, len - 1), Some('u' as usize)); // max
        assert_eq!(wm.quantile(0..3, 0), Some('b' as usize)); // zero-th in "tob" should be "b"

        let ranges = vec![0..3, 3..6];
        assert_eq!(wm.intersect(&ranges, 1), Some(vec!['o' as usize]));
    }

    #[test]
    fn test_serialize() {
        let text = "tobeornottobethatisthequestion";
        let mut seq = CompactVector::new(8).unwrap();
        seq.extend(text.chars().map(|c| c as usize)).unwrap();
        let wm = WaveletMatrix::<Rank9Sel>::new(seq).unwrap();

        let mut bytes = vec![];
        let size = wm.serialize_into(&mut bytes).unwrap();
        let other = WaveletMatrix::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(wm, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, wm.size_in_bytes());
    }
}
