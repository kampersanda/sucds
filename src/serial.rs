//! Serializers.

pub mod primitive;

use alloc::vec::Vec;

use crate::io::{Read, Write};
use crate::Result;

/// Upper bound of the bytes preallocated for a deserialized [`Vec`].
///
/// A length read from corrupted input can be huge, so the vector grows while reading
/// beyond this bound, and such input fails with an I/O error instead of aborting on allocation.
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
    /// # Panics
    ///
    /// Queries on the returned data structure may panic if the input is corrupted.
    fn deserialize_from_unchecked<R: Read>(reader: R) -> Result<Self> {
        Self::deserialize_from(reader)
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

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let x = if bool::deserialize_from(&mut reader)? {
            Some(S::deserialize_from(&mut reader)?)
        } else {
            None
        };
        Ok(x)
    }

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

    fn deserialize_from<R: Read>(reader: R) -> Result<Self> {
        deserialize_vec(reader, |r| S::deserialize_from(r))
    }

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

fn deserialize_vec<R, S, F>(mut reader: R, mut deserialize: F) -> Result<Vec<S>>
where
    R: Read,
    F: FnMut(&mut R) -> Result<S>,
{
    let len = usize::deserialize_from(&mut reader)?;
    let max_capa = MAX_PREALLOC_BYTES / core::mem::size_of::<S>().max(1);
    let mut vec = Vec::with_capacity(len.min(max_capa));
    for _ in 0..len {
        vec.push(deserialize(&mut reader)?);
    }
    Ok(vec)
}
