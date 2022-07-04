//! # `sucds`: Succinct data structures in Rust
//!
//! `sucds` contains some [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure) written in Rust.
//!
//! ## Data structures
//!
//! So far, the following data structures are implemented. Most of them are yet another Rust ports of implementations of [C++ Succinct library by Ottaviano](https://github.com/ot/succinct).
//! For a detailed description of each data structure, please see the [respective documentation](https://docs.rs/sucds/latest/sucds/).
//!
//! - [`BitVector`]
//!   - Bit vector in a plain format, supporting some utilities such as update, chunking, and predecessor queries.
//! - [`CompactVector`]
//!   - Compact vector in which each integer is represented in a fixed number of bits.
//! - [`RsBitVector`]
//!   - Rank/select data structure over bit vectors with Vigna's rank9 and hinted selection techniques.
//! - [`DArray`]
//!   - Constant-time select data structure over integer sets with the dense array technique by Okanohara and Sadakane.
//! - [`EliasFano`]
//!   - Compressed monotone sequence with Elias-Fano encoding.
//! - [`EliasFanoList`]
//!   - Compressed integer list with prefix-summed Elias-Fano encoding.
//! - [`WaveletMatrix`]
//!   - Space-efficient data structure providing myriad operations over integer sequences.
//!
//! ## Limitation
//!
//! This library is designed to run on 64-bit machines.
#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("`target_pointer_width` must be 64");

pub mod bit_vector;
pub mod broadword;
pub mod compact_vector;
pub mod darray;
pub mod elias_fano;
pub mod elias_fano_list;
mod intrinsics;
pub mod rs_bit_vector;
pub mod util;
pub mod wavelet_matrix;

pub use bit_vector::BitVector;
pub use compact_vector::CompactVector;
pub use darray::DArray;
pub use elias_fano::EliasFano;
pub use elias_fano::EliasFanoBuilder;
pub use elias_fano_list::EliasFanoList;
pub use rs_bit_vector::RsBitVector;
pub use wavelet_matrix::WaveletMatrix;
pub use wavelet_matrix::WaveletMatrixBuilder;

use util::IntIO;

/// Trait to serialize/deserialize data structures.
///
/// # Examples
///
/// ```
/// use sucds::{BitVector, Searial};
///
/// let bv = BitVector::from_bits([true, false, false, true]);
///
/// let mut bytes = vec![];
/// let size = bv.serialize_into(&mut bytes).unwrap();
/// let other = BitVector::deserialize_from(&bytes[..]).unwrap();
///
/// assert_eq!(bv, other);
/// assert_eq!(size, bytes.len());
/// assert_eq!(size, bv.size_in_bytes());
/// ```
pub trait Searial: Sized {
    /// Serializes the data structure into the writer,
    /// returning the number of serialized bytes.
    ///
    /// # Arguments
    ///
    /// - `writer`: [`std::io::Write`] variable.
    fn serialize_into<W: std::io::Write>(&self, writer: W) -> anyhow::Result<usize>;

    /// Deserializes the data structure from the reader.
    ///
    /// # Arguments
    ///
    /// - `reader`: [`std::io::Read`] variable.
    fn deserialize_from<R: std::io::Read>(reader: R) -> anyhow::Result<Self>;

    /// Returns the number of bytes to serialize the data structure.
    fn size_in_bytes(&self) -> usize;
}

impl<S> Searial for Option<S>
where
    S: Searial,
{
    fn serialize_into<W: std::io::Write>(&self, mut writer: W) -> anyhow::Result<usize> {
        let mut mem = 1;
        if let Some(x) = self {
            1u8.serialize_into(&mut writer)?;
            mem += x.serialize_into(&mut writer)?;
        } else {
            0u8.serialize_into(&mut writer)?;
        }
        Ok(mem)
    }

    fn deserialize_from<R: std::io::Read>(mut reader: R) -> anyhow::Result<Self> {
        let x = if u8::deserialize_from(&mut reader)? != 0 {
            Some(S::deserialize_from(&mut reader)?)
        } else {
            None
        };
        Ok(x)
    }

    fn size_in_bytes(&self) -> usize {
        self.as_ref().map_or(0, |x| x.size_in_bytes()) + 1
    }
}
