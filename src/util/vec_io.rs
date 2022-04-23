//! Utilities for writing/reading integers.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};
use std::mem::size_of;

use anyhow::Result;

use super::IntIO;

/// Trait to serialize/deserialize vectors of integers.
pub trait VecIO {
    /// The vector type.
    type Vec;

    /// Serializes the vector into the writer,
    /// returning the number of serialized bytes.
    ///
    /// # Arguments
    ///
    /// - `writer`: [`std::io::Write`] variable.
    fn serialize_into<W: Write>(&self, writer: W) -> Result<usize>;

    /// Deserializes the vector from the reader.
    ///
    /// # Arguments
    ///
    /// - `reader`: [`std::io::Read`] variable.
    fn deserialize_from<R: Read>(reader: R) -> Result<Self::Vec>;

    /// Returns the number of bytes to serialize the vector.
    fn size_in_bytes(&self) -> usize;
}

macro_rules! common_def {
    ($int:ident) => {
        impl VecIO for Vec<$int> {
            type Vec = Vec<$int>;

            fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
                let mut mem = self.len().serialize_into(&mut writer)?;
                for x in self {
                    mem += x.serialize_into(&mut writer)?;
                }
                Ok(mem)
            }

            fn deserialize_from<R: Read>(mut reader: R) -> Result<Self::Vec> {
                let len = usize::deserialize_from(&mut reader)?;
                let mut vec = Vec::with_capacity(len);
                for _ in 0..len {
                    vec.push($int::deserialize_from(&mut reader)?);
                }
                Ok(vec)
            }

            fn size_in_bytes(&self) -> usize {
                size_of::<u64>() + ($int::size_in_bytes() * self.len())
            }
        }
    };
}

common_def!(u8);
common_def!(u16);
common_def!(u32);
common_def!(u64);
common_def!(usize);
common_def!(i8);
common_def!(i16);
common_def!(i32);
common_def!(i64);
common_def!(isize);
