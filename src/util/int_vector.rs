use std::io::{Read, Write};
use std::mem::size_of;

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use num_traits::NumCast;

// How do we generalize signed/unsigned versions?
// If you know, please let me know.

/// Serializes the vector of primitive *unsigned* integers into the writer,
/// returning the number of serialized bytes.
///
/// # Arguments
///
/// - `vec`: Vector of primitive unsigned integers.
/// - `writer`: `std::io::Write` variable.
pub fn serialize_into<W, T>(vec: &[T], mut writer: W) -> Result<usize>
where
    W: Write,
    T: std::fmt::Debug + NumCast,
{
    writer.write_u64::<LittleEndian>(vec.len() as u64)?;
    match size_of::<T>() {
        1 => {
            for x in vec {
                writer.write_u8(
                    x.to_u8()
                        .ok_or_else(|| anyhow!("{:?} could not be converted to u8.", x))?,
                )?;
            }
        }
        2 => {
            for x in vec {
                writer.write_u16::<LittleEndian>(
                    x.to_u16()
                        .ok_or_else(|| anyhow!("{:?} could not be converted to u16.", x))?,
                )?;
            }
        }
        4 => {
            for x in vec {
                writer.write_u32::<LittleEndian>(
                    x.to_u32()
                        .ok_or_else(|| anyhow!("{:?} could not be converted to u32.", x))?,
                )?;
            }
        }
        8 => {
            for x in vec {
                writer.write_u64::<LittleEndian>(
                    x.to_u64()
                        .ok_or_else(|| anyhow!("{:?} could not be converted to u64.", x))?,
                )?;
            }
        }
        16 => {
            for x in vec {
                writer.write_u128::<LittleEndian>(
                    x.to_u128()
                        .ok_or_else(|| anyhow!("{:?} could not be converted to u128.", x))?,
                )?;
            }
        }
        _ => return Err(anyhow!("Invalid type: {:?}.", std::any::type_name::<T>())),
    }
    Ok(size_of::<u64>() + (size_of::<T>() * vec.len()))
}

/// Deserializes the vector of primitive *unsigned* integers from the reader.
///
/// # Arguments
///
/// - `reader`: `std::io::Read` variable.
pub fn deserialize_from<R, T>(mut reader: R) -> Result<Vec<T>>
where
    R: Read,
    T: NumCast,
{
    let len = reader.read_u64::<LittleEndian>()? as usize;
    let mut vec = Vec::with_capacity(len);
    match size_of::<T>() {
        1 => {
            for _ in 0..len {
                let x = reader.read_u8()?;
                vec.push(
                    T::from(x).ok_or_else(|| anyhow!("{:?} could not be converted from u8.", x))?,
                );
            }
        }
        2 => {
            for _ in 0..len {
                let x = reader.read_u16::<LittleEndian>()?;
                vec.push(
                    T::from(x)
                        .ok_or_else(|| anyhow!("{:?} could not be converted from u16.", x))?,
                );
            }
        }
        4 => {
            for _ in 0..len {
                let x = reader.read_u32::<LittleEndian>()?;
                vec.push(
                    T::from(x)
                        .ok_or_else(|| anyhow!("{:?} could not be converted from u32.", x))?,
                );
            }
        }
        8 => {
            for _ in 0..len {
                let x = reader.read_u64::<LittleEndian>()?;
                vec.push(
                    T::from(x)
                        .ok_or_else(|| anyhow!("{:?} could not be converted from u64.", x))?,
                );
            }
        }
        16 => {
            for _ in 0..len {
                let x = reader.read_u128::<LittleEndian>()?;
                vec.push(
                    T::from(x)
                        .ok_or_else(|| anyhow!("{:?} could not be converted from u128.", x))?,
                );
            }
        }
        _ => return Err(anyhow!("Invalid type: {:?}.", std::any::type_name::<T>())),
    }
    Ok(vec)
}

/// Returns the number of bytes to serialize the vector.
///
/// # Arguments
///
/// - `vec`: Vector of primitive integers.
pub const fn size_in_bytes<T>(vec: &[T]) -> usize {
    size_of::<u64>() + (size_of::<T>() * vec.len())
}

/// Module to serialize/deserialize signed integers.
pub mod singed {
    use super::*;

    /// Serializes the vector of primitive *signed* integers into the writer,
    /// returning the number of serialized bytes.
    ///
    /// # Arguments
    ///
    /// - `vec`: Vector of primitive signed integers.
    /// - `writer`: `std::io::Write` variable.
    pub fn serialize_into<W, T>(vec: &[T], mut writer: W) -> Result<usize>
    where
        W: Write,
        T: std::fmt::Debug + NumCast,
    {
        writer.write_u64::<LittleEndian>(vec.len() as u64)?;
        match size_of::<T>() {
            1 => {
                for x in vec {
                    writer.write_i8(
                        x.to_i8()
                            .ok_or_else(|| anyhow!("{:?} could not be converted to i8.", x))?,
                    )?;
                }
            }
            2 => {
                for x in vec {
                    writer.write_i16::<LittleEndian>(
                        x.to_i16()
                            .ok_or_else(|| anyhow!("{:?} could not be converted to i16.", x))?,
                    )?;
                }
            }
            4 => {
                for x in vec {
                    writer.write_i32::<LittleEndian>(
                        x.to_i32()
                            .ok_or_else(|| anyhow!("{:?} could not be converted to i32.", x))?,
                    )?;
                }
            }
            8 => {
                for x in vec {
                    writer.write_i64::<LittleEndian>(
                        x.to_i64()
                            .ok_or_else(|| anyhow!("{:?} could not be converted to i64.", x))?,
                    )?;
                }
            }
            16 => {
                for x in vec {
                    writer.write_i128::<LittleEndian>(
                        x.to_i128()
                            .ok_or_else(|| anyhow!("{:?} could not be converted to i128.", x))?,
                    )?;
                }
            }
            _ => return Err(anyhow!("Invalid type: {:?}.", std::any::type_name::<T>())),
        }
        Ok(size_of::<u64>() + (size_of::<T>() * vec.len()))
    }

    /// Deserializes the vector of primitive *signed* integers from the reader.
    ///
    /// # Arguments
    ///
    /// - `reader`: `std::io::Read` variable.
    pub fn deserialize_from<R, T>(mut reader: R) -> Result<Vec<T>>
    where
        R: Read,
        T: NumCast,
    {
        let len = reader.read_u64::<LittleEndian>()? as usize;
        let mut vec = Vec::with_capacity(len);
        match size_of::<T>() {
            1 => {
                for _ in 0..len {
                    let x = reader.read_i8()?;
                    vec.push(
                        T::from(x)
                            .ok_or_else(|| anyhow!("{:?} could not be converted from i8.", x))?,
                    );
                }
            }
            2 => {
                for _ in 0..len {
                    let x = reader.read_i16::<LittleEndian>()?;
                    vec.push(
                        T::from(x)
                            .ok_or_else(|| anyhow!("{:?} could not be converted from i16.", x))?,
                    );
                }
            }
            4 => {
                for _ in 0..len {
                    let x = reader.read_i32::<LittleEndian>()?;
                    vec.push(
                        T::from(x)
                            .ok_or_else(|| anyhow!("{:?} could not be converted from i32.", x))?,
                    );
                }
            }
            8 => {
                for _ in 0..len {
                    let x = reader.read_i64::<LittleEndian>()?;
                    vec.push(
                        T::from(x)
                            .ok_or_else(|| anyhow!("{:?} could not be converted from i64.", x))?,
                    );
                }
            }
            16 => {
                for _ in 0..len {
                    let x = reader.read_i128::<LittleEndian>()?;
                    vec.push(
                        T::from(x)
                            .ok_or_else(|| anyhow!("{:?} could not be converted from i128.", x))?,
                    );
                }
            }
            _ => return Err(anyhow!("Invalid type: {:?}.", std::any::type_name::<T>())),
        }
        Ok(vec)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! testconfig {
        (unsigned, $name:ident, $int:ty) => {
            #[test]
            fn $name() {
                let data: Vec<$int> = vec![1, 2, 3, 4];
                let mut buf = vec![];
                let size = serialize_into(&data, &mut buf).unwrap();
                assert_eq!(buf.len(), size);
                let other: Vec<$int> = deserialize_from(&buf[..]).unwrap();
                assert_eq!(data, other);
            }
        };
        (signed, $name:ident, $int:ty) => {
            #[test]
            fn $name() {
                let data: Vec<$int> = vec![-1, -2, -3, -4];
                let mut buf = vec![];
                let size = singed::serialize_into(&data, &mut buf).unwrap();
                assert_eq!(buf.len(), size);
                let other: Vec<$int> = singed::deserialize_from(&buf[..]).unwrap();
                assert_eq!(data, other);
            }
        };
    }

    testconfig!(unsigned, test_u8_vector, u8);
    testconfig!(unsigned, test_u16_vector, u16);
    testconfig!(unsigned, test_u32_vector, u32);
    testconfig!(unsigned, test_u64_vector, u64);
    testconfig!(unsigned, test_u128_vector, u128);
    testconfig!(signed, test_i8_vector, i8);
    testconfig!(signed, test_i16_vector, i16);
    testconfig!(signed, test_i32_vector, i32);
    testconfig!(signed, test_i64_vector, i64);
    testconfig!(signed, test_i128_vector, i128);
}
