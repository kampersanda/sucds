//! Utilities for serialize/deserialize integers.

use core::convert::TryFrom;

use super::Serializable;
use crate::io::{Read, Write};
use crate::Result;
use crate::SucdsError;

macro_rules! common_def {
    ($int:ident) => {
        impl Serializable for $int {
            fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
                writer.write_all(&self.to_le_bytes())?;
                Ok(core::mem::size_of::<Self>())
            }

            fn deserialize_from<R: Read>(mut reader: R) -> Result<Self> {
                let mut buf = [0; core::mem::size_of::<Self>()];
                reader.read_exact(&mut buf)?;
                Ok(Self::from_le_bytes(buf))
            }

            fn size_in_bytes(&self) -> usize {
                core::mem::size_of::<Self>()
            }

            fn size_of() -> Option<usize> {
                Some(core::mem::size_of::<Self>())
            }
        }
    };
}

common_def!(u8);
common_def!(u16);
common_def!(u32);
common_def!(u64);

common_def!(i8);
common_def!(i16);
common_def!(i32);
common_def!(i64);

/// `usize` is serialized as a fixed 64-bit little-endian integer so that
/// the format does not depend on the pointer width of the machine.
impl Serializable for usize {
    fn serialize_into<W: Write>(&self, writer: W) -> Result<usize> {
        (*self as u64).serialize_into(writer)
    }

    fn deserialize_from<R: Read>(reader: R) -> Result<Self> {
        let x = u64::deserialize_from(reader)?;
        Self::try_from(x).map_err(|_| {
            SucdsError::invalid_argument(format!(
                "the serialized value {x} does not fit in usize of this machine."
            ))
        })
    }

    fn size_in_bytes(&self) -> usize {
        core::mem::size_of::<u64>()
    }

    fn size_of() -> Option<usize> {
        Some(core::mem::size_of::<u64>())
    }
}

/// `isize` is serialized as a fixed 64-bit little-endian integer so that
/// the format does not depend on the pointer width of the machine.
impl Serializable for isize {
    fn serialize_into<W: Write>(&self, writer: W) -> Result<usize> {
        (*self as i64).serialize_into(writer)
    }

    fn deserialize_from<R: Read>(reader: R) -> Result<Self> {
        let x = i64::deserialize_from(reader)?;
        Self::try_from(x).map_err(|_| {
            SucdsError::invalid_argument(format!(
                "the serialized value {x} does not fit in isize of this machine."
            ))
        })
    }

    fn size_in_bytes(&self) -> usize {
        core::mem::size_of::<i64>()
    }

    fn size_of() -> Option<usize> {
        Some(core::mem::size_of::<i64>())
    }
}

impl Serializable for bool {
    fn serialize_into<W: Write>(&self, writer: W) -> Result<usize> {
        (*self as u8).serialize_into(writer)
    }

    fn deserialize_from<R: Read>(reader: R) -> Result<Self> {
        u8::deserialize_from(reader).map(|x| x != 0)
    }

    fn size_in_bytes(&self) -> usize {
        core::mem::size_of::<u8>()
    }

    fn size_of() -> Option<usize> {
        Some(core::mem::size_of::<u8>())
    }
}
