//! Serializers.

pub mod primitive;

use alloc::vec::Vec;

pub use bytes::Bytes;

use crate::io::{Read, Write};
use crate::Result;

/// Upper bound of the bytes preallocated for a deserialized [`Vec`].
///
/// A length read from corrupted input can be huge, so beyond this bound the vector grows while reading,
/// at most doubling each time, and such input fails with an I/O error instead of aborting on allocation.
const MAX_PREALLOC_BYTES: usize = 1 << 20;

/// Trait to serialize/deserialize data structures.
///
/// # Examples
///
/// ```
/// # fn main() -> sucds::Result<()> {
/// use sucds::{bit_vectors::BitVector, Serializable};
///
/// let bv = BitVector::from_bits([true, false, false, true]);
///
/// let mut bytes = vec![];
/// let size = bv.serialize_into(&mut bytes)?;
/// let other = BitVector::deserialize_from(&bytes[..])?;
///
/// assert_eq!(bv, other);
/// assert_eq!(size, bytes.len());
/// assert_eq!(size, bv.size_in_bytes());
/// # Ok(())
/// # }
/// ```
pub trait Serializable: Sized {
    /// Serializes the data structure into the writer,
    /// returning the number of serialized bytes.
    ///
    /// # Arguments
    ///
    /// - `writer`: [`Write`] variable.
    fn serialize_into<W: Write>(&self, writer: W) -> Result<usize>;

    /// Deserializes the data structure from the reader.
    ///
    /// # Arguments
    ///
    /// - `reader`: [`Read`] variable.
    ///
    /// # Complexity
    ///
    /// It depends on the data structure; see each implementation.
    /// Reading the data takes time linear in its size, and some data structures
    /// additionally check the consistency of their fields.
    fn deserialize_from<R: Read>(reader: R) -> Result<Self>;

    /// Deserializes the data structure from the reader, skipping costly consistency checks.
    ///
    /// [`Self::deserialize_from()`] rebuilds the rank/select indexes of some data structures
    /// (e.g., [`DArray`](crate::bit_vectors::DArray)) and compares them with the deserialized ones,
    /// which takes time linear in the data size. This function skips such checks for faster loading,
    /// and is intended for trusted input, e.g., data serialized by this crate itself.
    /// By default, it is the same as [`Self::deserialize_from()`].
    ///
    /// # Arguments
    ///
    /// - `reader`: [`Read`] variable.
    ///
    /// # Complexity
    ///
    /// It depends on the data structure; see each implementation.
    ///
    /// # Panics
    ///
    /// Queries on the returned data structure may panic if the input is corrupted.
    fn deserialize_from_unchecked<R: Read>(reader: R) -> Result<Self> {
        Self::deserialize_from(reader)
    }

    /// Deserializes the data structure from the shared bytes, advancing `bytes` past the read data.
    ///
    /// Data structures in this crate share their arrays with `bytes` instead of copying them,
    /// which is useful for memory-mapped files (see [`Bytes::from_owner()`]).
    /// The arrays are copied anyway if `bytes` is not aligned to 8 bytes or the machine is big-endian.
    /// By default, it copies the data through [`Self::deserialize_from()`].
    ///
    /// # Arguments
    ///
    /// - `bytes`: Bytes of the serialized data.
    ///
    /// # Complexity
    ///
    /// It depends on the data structure; see each implementation.
    fn deserialize_from_bytes(bytes: &mut Bytes) -> Result<Self> {
        read_from_bytes(bytes, |r| Self::deserialize_from(r))
    }

    /// Deserializes the data structure from the shared bytes, skipping costly consistency checks.
    ///
    /// This is the counterpart of [`Self::deserialize_from_unchecked()`] for [`Self::deserialize_from_bytes()`].
    /// Since the checks typically scan the whole data, this function is recommended for memory-mapped files
    /// to load them in time independent of the data size.
    /// By default, it is the same as [`Self::deserialize_from_bytes()`].
    ///
    /// # Arguments
    ///
    /// - `bytes`: Bytes of the serialized data.
    ///
    /// # Complexity
    ///
    /// It depends on the data structure; see each implementation.
    ///
    /// # Panics
    ///
    /// Queries on the returned data structure may panic if the input is corrupted.
    fn deserialize_from_bytes_unchecked(bytes: &mut Bytes) -> Result<Self> {
        Self::deserialize_from_bytes(bytes)
    }

    /// Returns the number of bytes to serialize the data structure.
    fn size_in_bytes(&self) -> usize;

    /// Returns the size of a primitive type in bytes (if the type is so).
    fn size_of() -> Option<usize> {
        None
    }
}

impl<S> Serializable for Option<S>
where
    S: Serializable,
{
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = 0;
        if let Some(x) = self {
            mem += true.serialize_into(&mut writer)?;
            mem += x.serialize_into(&mut writer)?;
        } else {
            mem += false.serialize_into(&mut writer)?;
        }
        Ok(mem)
    }

    /// Deserializes `Some(x)` or `None`.
    ///
    /// # Complexity
    ///
    /// That of deserializing `x`, if any.
    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        deserialize_option(&mut reader, true)
    }

    /// Deserializes `Some(x)` or `None`, without costly consistency checks of `x`.
    ///
    /// # Complexity
    ///
    /// That of deserializing `x` without the checks, if any.
    fn deserialize_from_unchecked<R: Read>(mut reader: R) -> Result<Self> {
        deserialize_option(&mut reader, false)
    }

    /// Deserializes `Some(x)` or `None` from the shared bytes.
    ///
    /// # Complexity
    ///
    /// That of deserializing `x` from the bytes, if any.
    fn deserialize_from_bytes(bytes: &mut Bytes) -> Result<Self> {
        deserialize_option(&mut Shared(bytes), true)
    }

    /// Deserializes `Some(x)` or `None` from the shared bytes, without costly consistency checks of `x`.
    ///
    /// # Complexity
    ///
    /// That of deserializing `x` from the bytes without the checks, if any.
    fn deserialize_from_bytes_unchecked(bytes: &mut Bytes) -> Result<Self> {
        deserialize_option(&mut Shared(bytes), false)
    }

    fn size_in_bytes(&self) -> usize {
        self.as_ref().map_or(0, |x| x.size_in_bytes()) + bool::size_of().unwrap()
    }
}

impl<S> Serializable for Vec<S>
where
    S: Serializable,
{
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = self.len().serialize_into(&mut writer)?;
        for x in self {
            mem += x.serialize_into(&mut writer)?;
        }
        if S::size_of().is_some() {
            mem += write_padding(&mut writer, mem)?;
        }
        Ok(mem)
    }

    /// Deserializes the elements.
    ///
    /// # Complexity
    ///
    /// The sum of those of deserializing the elements.
    /// The capacity grows geometrically, which takes amortized linear time in the length.
    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        deserialize_vec(&mut reader, true)
    }

    /// Deserializes the elements without costly consistency checks.
    ///
    /// # Complexity
    ///
    /// The sum of those of deserializing the elements without the checks.
    /// The capacity grows geometrically, which takes amortized linear time in the length.
    fn deserialize_from_unchecked<R: Read>(mut reader: R) -> Result<Self> {
        deserialize_vec(&mut reader, false)
    }

    /// Deserializes the elements from the shared bytes.
    ///
    /// # Complexity
    ///
    /// The sum of those of deserializing the elements from the bytes.
    fn deserialize_from_bytes(bytes: &mut Bytes) -> Result<Self> {
        deserialize_vec(&mut Shared(bytes), true)
    }

    /// Deserializes the elements from the shared bytes without costly consistency checks.
    ///
    /// # Complexity
    ///
    /// The sum of those of deserializing the elements from the bytes without the checks.
    fn deserialize_from_bytes_unchecked(bytes: &mut Bytes) -> Result<Self> {
        deserialize_vec(&mut Shared(bytes), false)
    }

    fn size_in_bytes(&self) -> usize {
        S::size_of().map_or_else(
            || usize::size_of().unwrap() + self.iter().fold(0, |acc, x| acc + x.size_in_bytes()),
            |m| usize::size_of().unwrap() + m * self.len() + padding_len(m * self.len()),
        )
    }
}

/// Source of serialized data, which is a reader or shared bytes.
///
/// Data structures implement their deserialization once on this trait
/// to support both [`Serializable::deserialize_from()`] and [`Serializable::deserialize_from_bytes()`].
pub(crate) trait Source {
    /// Deserializes `S`, checking its consistency if `checked` is true.
    fn read<S: Serializable>(&mut self, checked: bool) -> Result<S>;

    /// Skips `len` bytes.
    fn skip(&mut self, len: usize) -> Result<()>;
}

impl<R> Source for R
where
    R: Read,
{
    fn read<S: Serializable>(&mut self, checked: bool) -> Result<S> {
        if checked {
            S::deserialize_from(self)
        } else {
            S::deserialize_from_unchecked(self)
        }
    }

    fn skip(&mut self, len: usize) -> Result<()> {
        self.read_exact(&mut [0; 8][..len])?;
        Ok(())
    }
}

/// Shared bytes as a [`Source`].
pub(crate) struct Shared<'a>(pub &'a mut Bytes);

impl Source for Shared<'_> {
    fn read<S: Serializable>(&mut self, checked: bool) -> Result<S> {
        if checked {
            S::deserialize_from_bytes(self.0)
        } else {
            S::deserialize_from_bytes_unchecked(self.0)
        }
    }

    fn skip(&mut self, len: usize) -> Result<()> {
        read_from_bytes(self.0, |r| r.skip(len))
    }
}

/// Returns the number of padding bytes to align `size` bytes to 8 bytes.
///
/// Arrays of primitive integers are padded to a multiple of 8 bytes, and other serialized values
/// consist of 8-byte units, so that the arrays in the serialized bytes are aligned and
/// can be shared without copying.
pub(crate) const fn padding_len(size: usize) -> usize {
    (8 - size % 8) % 8
}

/// Writes the padding bytes after `size` bytes, returning the number of written bytes.
pub(crate) fn write_padding<W: Write>(mut writer: W, size: usize) -> Result<usize> {
    let len = padding_len(size);
    writer.write_all(&[0; 8][..len])?;
    Ok(len)
}

fn deserialize_option<Src, S>(src: &mut Src, checked: bool) -> Result<Option<S>>
where
    Src: Source,
    S: Serializable,
{
    let x = if src.read::<bool>(checked)? {
        Some(src.read(checked)?)
    } else {
        None
    };
    Ok(x)
}

/// Returns the number of elements preallocated within [`MAX_PREALLOC_BYTES`],
/// which is at least one so that deserialization always makes progress.
fn max_prealloc_len<S>() -> usize {
    (MAX_PREALLOC_BYTES / core::mem::size_of::<S>().max(1)).max(1)
}

fn deserialize_vec<Src, S>(src: &mut Src, checked: bool) -> Result<Vec<S>>
where
    Src: Source,
    S: Serializable,
{
    let len: usize = src.read(checked)?;
    let max_capa = max_prealloc_len::<S>();
    let mut vec = Vec::new();
    while vec.len() < len {
        // Grows geometrically to keep the copies amortized linear, but not beyond `len`
        // so that no extra capacity remains.
        let additional = (len - vec.len()).min(vec.len().max(max_capa));
        vec.reserve_exact(additional);
        for _ in 0..additional {
            vec.push(src.read(checked)?);
        }
    }
    if let Some(m) = S::size_of() {
        src.skip(padding_len(m * len))?;
    }
    Ok(vec)
}

/// Deserializes a value from `bytes` with `deserialize`, advancing `bytes` past the read data.
pub(crate) fn read_from_bytes<S, F>(bytes: &mut Bytes, deserialize: F) -> Result<S>
where
    F: FnOnce(&mut &[u8]) -> Result<S>,
{
    let mut reader = &bytes[..];
    let x = deserialize(&mut reader)?;
    let _ = bytes.split_to(bytes.len() - reader.len());
    Ok(x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec_exact_capacity() {
        // Longer than the preallocation bound of MAX_PREALLOC_BYTES / 8 elements.
        let vals: Vec<u64> = (0..300_000).collect();
        let mut bytes = vec![];
        vals.serialize_into(&mut bytes).unwrap();
        let other = Vec::<u64>::deserialize_from(&bytes[..]).unwrap();
        assert_eq!(vals, other);
        assert_eq!(other.capacity(), other.len());
    }

    #[test]
    fn test_max_prealloc_len() {
        assert_eq!(max_prealloc_len::<u64>(), MAX_PREALLOC_BYTES / 8);
        assert_eq!(max_prealloc_len::<()>(), MAX_PREALLOC_BYTES);
        // A type larger than the bound must still preallocate one element.
        assert_eq!(max_prealloc_len::<[u8; MAX_PREALLOC_BYTES + 1]>(), 1);
    }

    fn assert_default_round_trip<S>()
    where
        S: Serializable + Default + PartialEq + core::fmt::Debug,
    {
        let x = S::default();
        let mut bytes = vec![];
        x.serialize_into(&mut bytes).unwrap();
        assert_eq!(S::deserialize_from(&bytes[..]).unwrap(), x);
        assert_eq!(S::deserialize_from_unchecked(&bytes[..]).unwrap(), x);
    }

    fn assert_bytes_round_trip<S>(x: &S)
    where
        S: Serializable + PartialEq + core::fmt::Debug,
    {
        let mut src = vec![];
        let size = x.serialize_into(&mut src).unwrap();
        assert_eq!(size % 8, 0);
        // Trailing data must be left in the bytes.
        src.extend([1; 8]);
        for unchecked in [false, true] {
            let mut bytes = crate::storage::tests::aligned(&src);
            let y = if unchecked {
                S::deserialize_from_bytes_unchecked(&mut bytes).unwrap()
            } else {
                S::deserialize_from_bytes(&mut bytes).unwrap()
            };
            assert_eq!(&y, x);
            assert_eq!(&bytes[..], &[1; 8]);
        }
    }

    #[test]
    fn test_bytes_round_trip() {
        use crate::bit_vectors::{BitVector, DArray, Rank9Sel, SArray};
        use crate::char_sequences::WaveletMatrix;
        use crate::int_vectors::{CompactVector, DacsByte, DacsOpt, PrefixSummedEliasFano};
        use crate::mii_sequences::EliasFano;

        let bits: Vec<_> = (0..10_000).map(|i| i % 7 == 0 || i % 11 == 0).collect();
        let vals: Vec<u64> = (0..1_000).map(|i| (i * i) % 1_000).collect();

        assert_bytes_round_trip(&BitVector::from_bits(bits.iter().cloned()));
        assert_bytes_round_trip(
            &Rank9Sel::from_bits(bits.iter().cloned())
                .select1_hints()
                .select0_hints(),
        );
        assert_bytes_round_trip(
            &DArray::from_bits(bits.iter().cloned())
                .enable_rank()
                .enable_select0(),
        );
        assert_bytes_round_trip(&SArray::from_bits(bits.iter().cloned()).enable_rank());
        assert_bytes_round_trip(
            &EliasFano::from_bits(bits.iter().cloned())
                .unwrap()
                .enable_rank(),
        );
        assert_bytes_round_trip(&CompactVector::from_slice(&vals));
        assert_bytes_round_trip(&DacsByte::from_slice(&vals));
        assert_bytes_round_trip(&DacsOpt::from_slice(&vals, None).unwrap());
        assert_bytes_round_trip(&PrefixSummedEliasFano::from_slice(&vals).unwrap());
        assert_bytes_round_trip(
            &WaveletMatrix::new(CompactVector::from_slice(&vals), Rank9Sel::new).unwrap(),
        );
        assert_bytes_round_trip(
            &WaveletMatrix::new(CompactVector::from_slice(&vals), |bv| {
                DArray::from_bits(bv.iter()).enable_rank().enable_select0()
            })
            .unwrap(),
        );
        assert_bytes_round_trip(&vec![1u8, 2, 3]);
        assert_bytes_round_trip(&vec![1u16, 2, 3]);
        assert_bytes_round_trip(&Some(vec![1u32, 2, 3]));
        assert_bytes_round_trip(&true);
    }

    #[test]
    fn test_default_round_trip() {
        use crate::bit_vectors::{BitVector, DArray, Rank9Sel, SArray};
        use crate::char_sequences::WaveletMatrix;
        use crate::int_vectors::{CompactVector, DacsByte, DacsOpt, PrefixSummedEliasFano};
        use crate::mii_sequences::EliasFano;

        assert_default_round_trip::<BitVector>();
        assert_default_round_trip::<DArray>();
        assert_default_round_trip::<Rank9Sel>();
        assert_default_round_trip::<SArray>();
        assert_default_round_trip::<CompactVector>();
        assert_default_round_trip::<DacsByte>();
        assert_default_round_trip::<DacsOpt>();
        assert_default_round_trip::<PrefixSummedEliasFano>();
        assert_default_round_trip::<EliasFano>();
        assert_default_round_trip::<WaveletMatrix<Rank9Sel>>();
        assert_default_round_trip::<WaveletMatrix<DArray>>();
    }
}
