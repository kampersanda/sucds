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
pub mod intrinsics;
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
