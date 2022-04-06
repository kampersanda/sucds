//! Utilities for writing/reading integer vectors.
#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};
use std::mem::size_of;

use anyhow::Result;
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};

/// Returns the number of bytes to serialize the vector.
///
/// # Arguments
///
/// - `vec`: Vector of primitive integers.
pub const fn size_in_bytes<T>(vec: &[T]) -> usize {
    size_of::<u64>() + (size_of::<T>() * vec.len())
}

macro_rules! serialize_common {
    (single, $name:ident, $int:ty, $write:ident) => {
        /// Serializes integers of the type into a writer.
        pub fn $name<W: Write>(vec: &[$int], mut writer: W) -> Result<usize> {
            writer.write_u64::<LittleEndian>(vec.len() as u64)?;
            for &x in vec {
                writer.$write(x)?;
            }
            Ok(size_of::<u64>() + (size_of::<$int>() * vec.len()))
        }
    };
    (multi, $name:ident, $int:ty, $write:ident) => {
        /// Serializes integers of the type into a writer.
        pub fn $name<W: Write>(vec: &[$int], mut writer: W) -> Result<usize> {
            writer.write_u64::<LittleEndian>(vec.len() as u64)?;
            for &x in vec {
                writer.$write::<LittleEndian>(x)?;
            }
            Ok(size_of::<u64>() + (size_of::<$int>() * vec.len()))
        }
    };
    (word, $name:ident, $int:ty, $write:ident, $dst:ty) => {
        /// Serializes integers of the type into a writer.
        pub fn $name<W: Write>(vec: &[$int], mut writer: W) -> Result<usize> {
            writer.write_u64::<LittleEndian>(vec.len() as u64)?;
            for &x in vec {
                writer.$write::<LittleEndian>(x as $dst)?;
            }
            Ok(size_of::<u64>() + (size_of::<$int>() * vec.len()))
        }
    };
}

macro_rules! deserialize_common {
    (single, $name:ident, $int:ty, $read:ident) => {
        /// Deserializes integers of the type from a reader.
        pub fn $name<R: Read>(mut reader: R) -> Result<Vec<$int>> {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut vec = Vec::with_capacity(len);
            for _ in 0..len {
                vec.push(reader.$read()?);
            }
            Ok(vec)
        }
    };
    (multi, $name:ident, $int:ty, $read:ident) => {
        /// Deserializes integers of the type from a reader.
        pub fn $name<R: Read>(mut reader: R) -> Result<Vec<$int>> {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut vec = Vec::with_capacity(len);
            for _ in 0..len {
                vec.push(reader.$read::<LittleEndian>()?);
            }
            Ok(vec)
        }
    };
    (word, $name:ident, $int:ty, $read:ident) => {
        /// Deserializes integers of the type from a reader.
        pub fn $name<R: Read>(mut reader: R) -> Result<Vec<$int>> {
            let len = reader.read_u64::<LittleEndian>()? as usize;
            let mut vec = Vec::with_capacity(len);
            for _ in 0..len {
                vec.push(reader.$read::<LittleEndian>()? as $int);
            }
            Ok(vec)
        }
    };
}

serialize_common!(single, serialize_u8, u8, write_u8);
serialize_common!(multi, serialize_u16, u16, write_u16);
serialize_common!(multi, serialize_u32, u32, write_u32);
serialize_common!(multi, serialize_u64, u64, write_u64);
serialize_common!(word, serialize_usize, usize, write_u64, u64);

serialize_common!(single, serialize_i8, i8, write_i8);
serialize_common!(multi, serialize_i16, i16, write_i16);
serialize_common!(multi, serialize_i32, i32, write_i32);
serialize_common!(multi, serialize_i64, i64, write_i64);
serialize_common!(word, serialize_isize, isize, write_i64, i64);

deserialize_common!(single, deserialize_u8, u8, read_u8);
deserialize_common!(multi, deserialize_u16, u16, read_u16);
deserialize_common!(multi, deserialize_u32, u32, read_u32);
deserialize_common!(multi, deserialize_u64, u64, read_u64);
deserialize_common!(word, deserialize_usize, usize, read_u64);

deserialize_common!(single, deserialize_i8, i8, read_i8);
deserialize_common!(multi, deserialize_i16, i16, read_i16);
deserialize_common!(multi, deserialize_i32, i32, read_i32);
deserialize_common!(multi, deserialize_i64, i64, read_i64);
deserialize_common!(word, deserialize_isize, isize, read_i64);

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! testconfig {
        (unsigned_vector, $name:ident, $int:ty, $ser:ident, $deser:ident) => {
            #[test]
            fn $name() {
                let data: Vec<$int> = vec![1, 2, 3, 4];
                let mut buf = vec![];
                let size = $ser(&data, &mut buf).unwrap();
                assert_eq!(buf.len(), size);
                let other = $deser(&buf[..]).unwrap();
                assert_eq!(data, other);
            }
        };
        (signed_vector, $name:ident, $int:ty, $ser:ident, $deser:ident) => {
            #[test]
            fn $name() {
                let data: Vec<$int> = vec![-1, -2, -3, -4];
                let mut buf = vec![];
                let size = $ser(&data, &mut buf).unwrap();
                assert_eq!(buf.len(), size);
                let other = $deser(&buf[..]).unwrap();
                assert_eq!(data, other);
            }
        };
    }

    testconfig!(
        unsigned_vector,
        test_u8_vector,
        u8,
        serialize_u8,
        deserialize_u8
    );
    testconfig!(
        unsigned_vector,
        test_u16_vector,
        u16,
        serialize_u16,
        deserialize_u16
    );
    testconfig!(
        unsigned_vector,
        test_u32_vector,
        u32,
        serialize_u32,
        deserialize_u32
    );
    testconfig!(
        unsigned_vector,
        test_u64_vector,
        u64,
        serialize_u64,
        deserialize_u64
    );
    testconfig!(
        unsigned_vector,
        test_usize_vector,
        usize,
        serialize_usize,
        deserialize_usize
    );
    testconfig!(
        signed_vector,
        test_i8_vector,
        i8,
        serialize_i8,
        deserialize_i8
    );
    testconfig!(
        signed_vector,
        test_i16_vector,
        i16,
        serialize_i16,
        deserialize_i16
    );
    testconfig!(
        signed_vector,
        test_i32_vector,
        i32,
        serialize_i32,
        deserialize_i32
    );
    testconfig!(
        signed_vector,
        test_i64_vector,
        i64,
        serialize_i64,
        deserialize_i64
    );
    testconfig!(
        signed_vector,
        test_isize_vector,
        isize,
        serialize_isize,
        deserialize_isize
    );
}
