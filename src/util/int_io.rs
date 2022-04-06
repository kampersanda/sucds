//! Utilities for writing/reading integers.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};
use std::mem::size_of;

use anyhow::Result;

macro_rules! common {
    (write, $name:ident, $int:ident, $docstring:literal) => {
        #[doc = $docstring]
        pub fn $name<W: Write>(x: $int, mut writer: W) -> Result<usize> {
            writer.write_all(&x.to_le_bytes())?;
            Ok(size_of::<$int>())
        }
    };
    (read, $name:ident, $int:ident, $docstring:literal) => {
        #[doc = $docstring]
        pub fn $name<R: Read>(mut reader: R) -> Result<$int> {
            let mut buf = [0; size_of::<$int>()];
            reader.read_exact(&mut buf)?;
            Ok($int::from_le_bytes(buf))
        }
    };
}

common!(
    write,
    write_u8,
    u8,
    "Writes an integer of type [`u8`] to a writable instance."
);
common!(
    write,
    write_u16,
    u16,
    "Writes an integer of type [`u16`] to a writable instance."
);
common!(
    write,
    write_u32,
    u32,
    "Writes an integer of type [`u32`] to a writable instance."
);
common!(
    write,
    write_u64,
    u64,
    "Writes an integer of type [`u64`] to a writable instance."
);
common!(
    write,
    write_usize,
    usize,
    "Writes an integer of type [`usize`] to a writable instance."
);
common!(
    write,
    write_i8,
    i8,
    "Writes an integer of type [`i8`] to a writable instance."
);
common!(
    write,
    write_i16,
    i16,
    "Writes an integer of type [`i16`] to a writable instance."
);
common!(
    write,
    write_i32,
    i32,
    "Writes an integer of type [`i32`] to a writable instance."
);
common!(
    write,
    write_i64,
    i64,
    "Writes an integer of type [`i64`] to a writable instance."
);
common!(
    write,
    write_isize,
    isize,
    "Writes an integer of type [`isize`] to a writable instance."
);

common!(
    read,
    read_u8,
    u8,
    "Reads an integer of type [`u8`] from a readable instance."
);
common!(
    read,
    read_u16,
    u16,
    "Reads an integer of type [`u16`] from a readable instance."
);
common!(
    read,
    read_u32,
    u32,
    "Reads an integer of type [`u32`] from a readable instance."
);
common!(
    read,
    read_u64,
    u64,
    "Reads an integer of type [`u64`] from a readable instance."
);
common!(
    read,
    read_usize,
    usize,
    "Reads an integer of type [`usize`] from a readable instance."
);
common!(
    read,
    read_i8,
    i8,
    "Reads an integer of type [`i8`] from a readable instance."
);
common!(
    read,
    read_i16,
    i16,
    "Reads an integer of type [`i16`] from a readable instance."
);
common!(
    read,
    read_i32,
    i32,
    "Reads an integer of type [`i32`] from a readable instance."
);
common!(
    read,
    read_i64,
    i64,
    "Reads an integer of type [`i64`] from a readable instance."
);
common!(
    read,
    read_isize,
    isize,
    "Reads an integer of type [`isize`] from a readable instance."
);
