//! Utilities for serialize/deserialize integers.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};

use anyhow::Result;

use super::Serializable;

macro_rules! common_def {
    ($int:ident) => {
        impl Serializable for $int {
            fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
                writer.write_all(&self.to_le_bytes())?;
                Ok(std::mem::size_of::<Self>())
            }

            fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
                let mut buf = [0; std::mem::size_of::<Self>()];
                reader.read_exact(&mut buf)?;
                Ok(Self::from_le_bytes(buf))
            }

            fn size_in_bytes(&self) -> usize {
                std::mem::size_of::<Self>()
            }

            fn size_of() -> Option<usize> {
                Some(std::mem::size_of::<Self>())
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

impl Serializable for bool {
    fn serialize_into<W: Write>(&self, writer: W) -> Result<usize> {
        (*self as u8).serialize_into(writer)
    }

    fn deserialize_from<R: Read>(reader: R) -> Result<Self> {
        u8::deserialize_from(reader).map(|x| x != 0)
    }

    fn size_in_bytes(&self) -> usize {
        std::mem::size_of::<u8>()
    }

    fn size_of() -> Option<usize> {
        Some(std::mem::size_of::<u8>())
    }
}
