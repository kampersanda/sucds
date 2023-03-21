//! Utilities for serialization.
#![cfg(target_pointer_width = "64")]

pub mod primitive;

use std::io::{Read, Write};

use anyhow::Result;

/// Trait to serialize/deserialize data structures.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
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

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
        let len = usize::deserialize_from(&mut reader)?;
        let mut vec = Self::with_capacity(len);
        for _ in 0..len {
            vec.push(S::deserialize_from(&mut reader)?);
        }
        Ok(vec)
    }

    fn size_in_bytes(&self) -> usize {
        S::size_of().map_or_else(
            || usize::size_of().unwrap() + self.iter().fold(0, |acc, x| acc + x.size_in_bytes()),
            |m| usize::size_of().unwrap() + m * self.len(),
        )
    }
}
