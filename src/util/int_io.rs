//! Utilities for serialize/deserialize integers.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};
use std::mem::size_of;

use anyhow::Result;

/// Trait to serialize/deserialize integers of primitive types.
pub trait IntIO {
    /// The integer type.
    type Int;

    /// Serializes the integer into the writer,
    /// returning the number of serialized bytes.
    ///
    /// # Arguments
    ///
    /// - `writer`: [`std::io::Write`] variable.
    fn serialize_into<W: Write>(self, writer: W) -> Result<usize>;

    /// Deserializes the integer from the reader.
    ///
    /// # Arguments
    ///
    /// - `reader`: [`std::io::Read`] variable.
    fn deserialize_from<R: Read>(reader: R) -> Result<Self::Int>;

    /// Returns the number of bytes to serialize the integer.
    fn size_in_bytes() -> usize {
        size_of::<Self::Int>()
    }
}

macro_rules! common_def {
    ($int:ident) => {
        impl IntIO for $int {
            type Int = Self;

            fn serialize_into<W: Write>(self, mut writer: W) -> Result<usize> {
                writer.write_all(&self.to_le_bytes())?;
                Ok(size_of::<Self::Int>())
            }

            fn deserialize_from<R: Read>(mut reader: R) -> Result<Self::Int> {
                let mut buf = [0; size_of::<Self::Int>()];
                reader.read_exact(&mut buf)?;
                Ok(Self::Int::from_le_bytes(buf))
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

impl IntIO for bool {
    type Int = Self;

    fn serialize_into<W: Write>(self, mut writer: W) -> Result<usize> {
        writer.write_all(&(self as u8).to_le_bytes())?;
        Ok(size_of::<Self::Int>())
    }

    fn deserialize_from<R: Read>(mut reader: R) -> Result<Self::Int> {
        let mut buf = [0; size_of::<Self::Int>()];
        reader.read_exact(&mut buf)?;
        Ok(u8::from_le_bytes(buf) != 0)
    }
}
