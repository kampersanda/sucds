//! Utilities in Sucds.
#![cfg(target_pointer_width = "64")]

pub mod int_io;

use crate::{broadword, Searial};

pub use int_io::IntIO;

impl<S> Searial for Vec<S>
where
    S: IntIO + Copy,
{
    fn serialize_into<W: std::io::Write>(&self, mut writer: W) -> anyhow::Result<usize> {
        let mut mem = self.len().serialize_into(&mut writer)?;
        for &x in self {
            mem += x.serialize_into(&mut writer)?;
        }
        Ok(mem)
    }

    fn deserialize_from<R: std::io::Read>(mut reader: R) -> anyhow::Result<Self> {
        let len = usize::deserialize_from(&mut reader)?;
        let mut vec = Self::with_capacity(len);
        for _ in 0..len {
            vec.push(S::deserialize_from(&mut reader)?);
        }
        Ok(vec)
    }

    fn size_in_bytes(&self) -> usize {
        usize::size_in_bytes() + S::size_in_bytes() * self.len()
    }
}

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
