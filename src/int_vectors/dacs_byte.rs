//! Compressed integer sequence using Directly Addressable Codes (DACs) in a simple bytewise scheme.

use alloc::vec::Vec;

use core::convert::TryFrom;

use crate::bit_vectors::{self, BitVector, Rank, Rank9Sel};
use crate::int_vectors::Access;
use crate::io::{Read, Write};
use crate::serial::{Bytes, Shared, Source};
use crate::storage::Storage;
use crate::utils;
use crate::Result;
use crate::Serializable;

const LEVEL_WIDTH: usize = 8;
const LEVEL_MASK: u64 = (1 << LEVEL_WIDTH) - 1;

/// Compressed integer sequence using Directly Addressable Codes (DACs) in a simple bytewise scheme.
///
/// DACs are a compact representation of an integer sequence consisting of many small values.
/// [`DacsByte`] is a simple variant and uses [`Vec<u8>`] for each level to obtain faster
/// operations than [`DacsOpt`](super::DacsOpt).
///
/// # Memory complexity
///
/// $`\textrm{DAC}(A) + o(\textrm{DAC}(A)/b) + O(\lg u)`$ bits where
///
/// - $`u`$ is the maximum value plus 1,
/// - $`b`$ is the length in bits assigned for each level with DACs (here $`b = 8`$), and
/// - $`\textrm{DAC}(A)`$ is the length in bits of the encoded sequence from an original sequence $`A`$ with DACs.
///
/// # Examples
///
/// ```
/// # fn main() -> sucds::Result<()> {
/// use sucds::int_vectors::{DacsByte, Access};
///
/// let seq = DacsByte::from_slice(&[5u64, 0, 100000, 334]);
///
/// assert_eq!(seq.access(0), Some(5));
/// assert_eq!(seq.access(1), Some(0));
/// assert_eq!(seq.access(2), Some(100000));
/// assert_eq!(seq.access(3), Some(334));
///
/// assert_eq!(seq.len(), 4);
/// assert_eq!(seq.num_levels(), 3);
/// # Ok(())
/// # }
/// ```
///
/// # References
///
/// - N. R. Brisaboa, S. Ladra, and G. Navarro, "DACs: Bringing direct access to variable-length
///   codes." Information Processing & Management, 49(1), 392-404, 2013.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DacsByte {
    data: Vec<Storage<u8>>,
    flags: Vec<Rank9Sel>,
}

impl DacsByte {
    /// Builds DACs by assigning 8 bits to represent each level.
    ///
    /// # Arguments
    ///
    /// - `vals`: Slice of integers to be stored.
    ///
    pub fn from_slice<T>(vals: &[T]) -> Self
    where
        T: Into<u64> + Copy,
    {
        if vals.is_empty() {
            return Self::default();
        }

        let mut maxv = 0;
        for x in vals {
            maxv = maxv.max((*x).into());
        }
        let num_bits = utils::needed_bits(maxv);
        let num_levels = utils::ceiled_divide(num_bits, LEVEL_WIDTH);
        assert_ne!(num_levels, 0);

        if num_levels == 1 {
            let data: Vec<_> = vals
                .iter()
                .map(|x| u8::try_from((*x).into()).unwrap())
                .collect();
            return Self {
                data: vec![data.into()],
                flags: vec![],
            };
        }

        let mut data = vec![vec![]; num_levels];
        let mut flags = vec![BitVector::default(); num_levels - 1];

        for x in vals {
            let mut x = (*x).into();
            for j in 0..num_levels {
                data[j].push(u8::try_from(x & LEVEL_MASK).unwrap());
                x >>= LEVEL_WIDTH;
                if j == num_levels - 1 {
                    assert_eq!(x, 0);
                    break;
                } else if x == 0 {
                    flags[j].push_bit(false);
                    break;
                }
                flags[j].push_bit(true);
            }
        }

        let data = data.into_iter().map(Storage::from).collect();
        let flags = flags.into_iter().map(Rank9Sel::new).collect();
        Self { data, flags }
    }

    /// Creates an iterator for enumerating integers.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> sucds::Result<()> {
    /// use sucds::int_vectors::DacsByte;
    ///
    /// let seq = DacsByte::from_slice(&[5u64, 0, 100000, 334]);
    /// let mut it = seq.iter();
    ///
    /// assert_eq!(it.next(), Some(5));
    /// assert_eq!(it.next(), Some(0));
    /// assert_eq!(it.next(), Some(100000));
    /// assert_eq!(it.next(), Some(334));
    /// assert_eq!(it.next(), None);
    /// # Ok(())
    /// # }
    /// ```
    pub const fn iter(&self) -> Iter<'_> {
        Iter::new(self)
    }

    /// Gets the number of integers.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.data[0].len()
    }

    /// Checks if the vector is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets the number of levels.
    #[inline(always)]
    pub fn num_levels(&self) -> usize {
        self.data.len()
    }

    /// Gets the number of bits for each level.
    #[inline(always)]
    pub fn widths(&self) -> Vec<usize> {
        self.data.iter().map(|_| LEVEL_WIDTH).collect()
    }
}

impl Default for DacsByte {
    fn default() -> Self {
        Self {
            // Needs a single level at least.
            data: vec![Storage::default()],
            flags: vec![],
        }
    }
}

impl Access for DacsByte {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    ///
    /// # Complexity
    ///
    /// $`O( \ell_{pos} )`$ where $`\ell_{pos}`$ is the number of levels corresponding to
    /// the `pos`-th integer.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() -> sucds::Result<()> {
    /// use sucds::int_vectors::{DacsByte, Access};
    ///
    /// let seq = DacsByte::from_slice(&[5u64, 999, 334]);
    ///
    /// assert_eq!(seq.access(0), Some(5));
    /// assert_eq!(seq.access(1), Some(999));
    /// assert_eq!(seq.access(2), Some(334));
    /// assert_eq!(seq.access(3), None);
    /// # Ok(())
    /// # }
    /// ```
    fn access(&self, mut pos: usize) -> Option<u64> {
        if self.len() <= pos {
            return None;
        }
        let mut x = 0;
        for j in 0..self.num_levels() {
            x |= u64::from(self.data[j][pos]) << (j * LEVEL_WIDTH);
            if j == self.num_levels() - 1
                || !bit_vectors::Access::access(&self.flags[j], pos).unwrap()
            {
                break;
            }
            pos = self.flags[j].rank1(pos).unwrap();
        }
        Some(x)
    }
}

/// Iterator for enumerating integers, created by [`DacsByte::iter()`].
pub struct Iter<'a> {
    seq: &'a DacsByte,
    pos: usize,
}

impl<'a> Iter<'a> {
    /// Creates a new iterator.
    pub const fn new(seq: &'a DacsByte) -> Self {
        Self { seq, pos: 0 }
    }
}

impl Iterator for Iter<'_> {
    type Item = u64;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.seq.len() {
            let x = self.seq.access(self.pos).unwrap();
            self.pos += 1;
            Some(x)
        } else {
            None
        }
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let rem = self.seq.len() - self.pos;
        (rem, Some(rem))
    }
}

impl Serializable for DacsByte {
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        mem += self.data.serialize_into(&mut writer)?;
        mem += self.flags.serialize_into(&mut writer)?;
        Ok(mem)
    }

    /// Deserializes the data structure and checks its consistency.
    ///
    /// # Complexity
    ///
    /// Linear in the size of the data, including the time to check the [`Rank9Sel`] of each level
    /// by rebuilding its index.
    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        Self::deserialize_with(&mut reader, true)
    }

    /// Deserializes the data structure without costly consistency checks.
    ///
    /// # Complexity
    ///
    /// Linear in the size of the data.
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
        self.data.size_in_bytes() + self.flags.size_in_bytes()
    }
}

impl DacsByte {
    fn deserialize_with<Src: Source>(src: &mut Src, checked: bool) -> Result<Self> {
        Ok(Self {
            data: src.read(checked)?,
            flags: src.read(checked)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::tests::aligned;

    #[test]
    fn test_deserialize_from_bytes_shared() {
        let seq = DacsByte::from_slice(&[0xFFFFu64, 0xFF, 0xF, 0xFFFFF, 0xF]);
        let mut src = vec![];
        seq.serialize_into(&mut src).unwrap();
        let other = DacsByte::deserialize_from_bytes_unchecked(&mut aligned(&src)).unwrap();
        assert_eq!(seq, other);
        if cfg!(target_endian = "little") {
            assert!(other.data.iter().all(|d| d.is_shared()));
        }
    }

    #[test]
    fn test_deserialize_from_bytes_huge_level() {
        // One level of `usize::MAX` bytes.
        let mut src = 1u64.to_le_bytes().to_vec();
        src.extend((usize::MAX as u64).to_le_bytes());
        let e = DacsByte::deserialize_from_bytes(&mut aligned(&src));
        assert!(matches!(e, Err(crate::SucdsError::InvalidData(_))));
    }

    #[test]
    fn test_basic() {
        let seq = DacsByte::from_slice(&[0xFFFFu64, 0xFF, 0xF, 0xFFFFF, 0xF]);

        assert_eq!(
            seq.data,
            vec![
                vec![0xFF, 0xFF, 0xF, 0xFF, 0xF].into(),
                vec![0xFF, 0xFF].into(),
                vec![0xF].into()
            ]
        );

        assert_eq!(
            seq.flags,
            vec![
                Rank9Sel::from_bits([true, false, false, true, false]),
                Rank9Sel::from_bits([false, true])
            ]
        );

        assert!(!seq.is_empty());
        assert_eq!(seq.len(), 5);
        assert_eq!(seq.num_levels(), 3);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH, LEVEL_WIDTH, LEVEL_WIDTH]);

        assert_eq!(seq.access(0), Some(0xFFFF));
        assert_eq!(seq.access(1), Some(0xFF));
        assert_eq!(seq.access(2), Some(0xF));
        assert_eq!(seq.access(3), Some(0xFFFFF));
        assert_eq!(seq.access(4), Some(0xF));
    }

    #[test]
    fn test_empty() {
        let seq = DacsByte::from_slice::<u64>(&[]);
        assert!(seq.is_empty());
        assert_eq!(seq.len(), 0);
        assert_eq!(seq.num_levels(), 1);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH]);
    }

    #[test]
    fn test_all_zeros() {
        let seq = DacsByte::from_slice(&[0u64, 0, 0, 0]);
        assert!(!seq.is_empty());
        assert_eq!(seq.len(), 4);
        assert_eq!(seq.num_levels(), 1);
        assert_eq!(seq.widths(), vec![LEVEL_WIDTH]);
        assert_eq!(seq.access(0), Some(0));
        assert_eq!(seq.access(1), Some(0));
        assert_eq!(seq.access(2), Some(0));
        assert_eq!(seq.access(3), Some(0));
    }

    #[test]
    fn test_serialize() {
        let mut bytes = vec![];
        let seq = DacsByte::from_slice(&[0xFFFFFu32, 0xFF, 0xF, 0xFFFFF, 0xF]);
        let size = seq.serialize_into(&mut bytes).unwrap();
        let other = DacsByte::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(seq, other);
        let other = DacsByte::deserialize_from_unchecked(&bytes[..]).unwrap();
        assert_eq!(seq, other);
        assert_eq!(size, bytes.len());
        assert_eq!(size, seq.size_in_bytes());
    }

    #[test]
    fn test_deserialize_unchecked_forwarded() {
        use crate::bit_vectors::BitVector;

        // A Rank9Sel whose index was built for another bit vector.
        let r9s = Rank9Sel::from_bits([true, false, true]);
        let mut r9s_bytes = vec![];
        r9s.serialize_into(&mut r9s_bytes).unwrap();
        let bv = BitVector::from_bits([true, true, true]);
        let mut bytes = vec![];
        bv.serialize_into(&mut bytes).unwrap();
        bytes.extend_from_slice(&r9s_bytes[bv.size_in_bytes()..]);
        let bad = Rank9Sel::deserialize_from_unchecked(&bytes[..]).unwrap();

        let seq = DacsByte {
            data: vec![vec![1, 2, 3].into()],
            flags: vec![bad],
        };
        let mut bytes = vec![];
        seq.serialize_into(&mut bytes).unwrap();
        let e = DacsByte::deserialize_from(&bytes[..]);
        assert!(matches!(e, Err(crate::SucdsError::InvalidData(_))));
        assert!(DacsByte::deserialize_from_unchecked(&bytes[..]).is_ok());
    }

    #[test]
    fn test_iter_size_hint() {
        let seq = DacsByte::from_slice(&[1u64, 2, 3, 4]);
        let mut it = seq.iter();
        assert_eq!(it.size_hint(), (4, Some(4)));
        it.next();
        it.next();
        assert_eq!(it.size_hint(), (2, Some(2)));
        it.next();
        it.next();
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
        assert_eq!(it.size_hint(), (0, Some(0)));
    }
}
