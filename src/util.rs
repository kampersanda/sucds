#![cfg(target_pointer_width = "64")]

use std::io::{Read, Write};
use std::mem::size_of;

use anyhow::{anyhow, Result};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use num_traits::{FromPrimitive, ToPrimitive};

use crate::broadword;

/// Returns the number of bits to represent `x` at least.
///
/// # Example
///
/// ```
/// use sucds::util::needed_bits;
///
/// assert_eq!(needed_bits(0), 1);
/// assert_eq!(needed_bits(1), 1);
/// assert_eq!(needed_bits(2), 2);
/// assert_eq!(needed_bits(255), 8);
/// assert_eq!(needed_bits(256), 9);
/// ```
pub fn needed_bits(x: usize) -> usize {
    broadword::msb(x).map_or(1, |n| n + 1)
}

/// Serializes the vector of primitive integers into the writer,
/// returning the number of serialized bytes.
///
/// # Arguments
///
/// - `vec`: Vector of primitive integers.
/// - `writer`: Writer.
pub fn serialize_int_vector<W, T>(vec: &[T], mut writer: W) -> Result<usize>
where
    W: Write,
    T: ToPrimitive,
{
    writer.write_u64::<LittleEndian>(vec.len() as u64)?;
    match size_of::<T>() {
        1 => {
            for x in vec {
                writer.write_u8(x.to_u8().unwrap())?;
            }
        }
        2 => {
            for x in vec {
                writer.write_u16::<LittleEndian>(x.to_u16().unwrap())?;
            }
        }
        4 => {
            for x in vec {
                writer.write_u32::<LittleEndian>(x.to_u32().unwrap())?;
            }
        }
        8 => {
            for x in vec {
                writer.write_u64::<LittleEndian>(x.to_u64().unwrap())?;
            }
        }
        16 => {
            for x in vec {
                writer.write_u128::<LittleEndian>(x.to_u128().unwrap())?;
            }
        }
        _ => return Err(anyhow!("Invalid int type.")),
    }
    Ok(size_of::<u64>() + (size_of::<T>() * vec.len()))
}

/// Deserializes the vector of primitive integers from the reader.
///
/// # Arguments
///
/// - `reader`: Reader.
pub fn deserialize_int_vector<R, T>(mut reader: R) -> Result<Vec<T>>
where
    R: Read,
    T: FromPrimitive,
{
    let len = reader.read_u64::<LittleEndian>()? as usize;
    let mut vec = Vec::with_capacity(len);
    match size_of::<T>() {
        1 => {
            for _ in 0..len {
                vec.push(T::from_u8(reader.read_u8()?).unwrap());
            }
        }
        2 => {
            for _ in 0..len {
                vec.push(T::from_u16(reader.read_u16::<LittleEndian>()?).unwrap());
            }
        }
        4 => {
            for _ in 0..len {
                vec.push(T::from_u32(reader.read_u32::<LittleEndian>()?).unwrap());
            }
        }
        8 => {
            for _ in 0..len {
                vec.push(T::from_u64(reader.read_u64::<LittleEndian>()?).unwrap());
            }
        }
        16 => {
            for _ in 0..len {
                vec.push(T::from_u128(reader.read_u128::<LittleEndian>()?).unwrap());
            }
        }
        _ => return Err(anyhow!("Invalid int type.")),
    }
    Ok(vec)
}
