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
    /// Data structures supporting zero-copy deserialization share their arrays with `bytes`
    /// instead of copying them, which is useful for memory-mapped files
    /// (see [`Bytes::from_owner()`]). The arrays are copied anyway if `bytes` is not aligned for them
    /// or the machine is big-endian.
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
        let x = if bool::deserialize_from(&mut reader)? {
            Some(S::deserialize_from(&mut reader)?)
        } else {
            None
        };
        Ok(x)
    }

    /// Deserializes `Some(x)` or `None`, without costly consistency checks of `x`.
    ///
    /// # Complexity
    ///
    /// That of deserializing `x` without the checks, if any.
    fn deserialize_from_unchecked<R: Read>(mut reader: R) -> Result<Self> {
        let x = if bool::deserialize_from(&mut reader)? {
            Some(S::deserialize_from_unchecked(&mut reader)?)
        } else {
            None
        };
        Ok(x)
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
        Ok(mem)
    }

    /// Deserializes the elements.
    ///
    /// # Complexity
    ///
    /// The sum of those of deserializing the elements.
    /// The capacity grows geometrically, which takes amortized linear time in the length.
    fn deserialize_from<R: Read>(reader: R) -> Result<Self> {
        deserialize_vec(reader, |r| S::deserialize_from(r))
    }

    /// Deserializes the elements without costly consistency checks.
    ///
    /// # Complexity
    ///
    /// The sum of those of deserializing the elements without the checks.
    /// The capacity grows geometrically, which takes amortized linear time in the length.
    fn deserialize_from_unchecked<R: Read>(reader: R) -> Result<Self> {
        deserialize_vec(reader, |r| S::deserialize_from_unchecked(r))
    }

    fn size_in_bytes(&self) -> usize {
        S::size_of().map_or_else(
            || usize::size_of().unwrap() + self.iter().fold(0, |acc, x| acc + x.size_in_bytes()),
            |m| usize::size_of().unwrap() + m * self.len(),
        )
    }
}

/// Returns the number of elements preallocated within [`MAX_PREALLOC_BYTES`],
/// which is at least one so that deserialization always makes progress.
fn max_prealloc_len<S>() -> usize {
    (MAX_PREALLOC_BYTES / core::mem::size_of::<S>().max(1)).max(1)
}

fn deserialize_vec<R, S, F>(mut reader: R, mut deserialize: F) -> Result<Vec<S>>
where
    R: Read,
    F: FnMut(&mut R) -> Result<S>,
{
    let len = usize::deserialize_from(&mut reader)?;
    let max_capa = max_prealloc_len::<S>();
    let mut vec = Vec::new();
    while vec.len() < len {
        // Grows geometrically to keep the copies amortized linear, but not beyond `len`
        // so that no extra capacity remains.
        let additional = (len - vec.len()).min(vec.len().max(max_capa));
        vec.reserve_exact(additional);
        for _ in 0..additional {
            vec.push(deserialize(&mut reader)?);
        }
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
