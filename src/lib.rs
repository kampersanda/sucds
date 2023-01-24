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
//! - [`DacsOpt`] and [`DacsByte`]
//!   - Compressed integer list with directly addressable codes.
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
pub mod dacs_byte;
pub mod dacs_opt;
pub mod darray;
pub mod elias_fano;
pub mod elias_fano_list;
mod intrinsics;
pub mod rs_bit_vector;
pub mod serial;
pub mod util;
pub mod wavelet_matrix;

pub use bit_vector::BitVector;
pub use compact_vector::CompactVector;
pub use dacs_byte::DacsByte;
pub use dacs_opt::DacsOpt;
pub use darray::DArray;
pub use elias_fano::EliasFano;
pub use elias_fano::EliasFanoBuilder;
pub use elias_fano_list::EliasFanoList;
pub use rs_bit_vector::RsBitVector;
pub use serial::Searial;
pub use wavelet_matrix::WaveletMatrix;
pub use wavelet_matrix::WaveletMatrixBuilder;

// NOTE(kampersanda): We should use `get()` because it has been already used in most std
// containers with different type annotations.

/// An interface for accessing elements on bit arrays.
pub trait BitGetter {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    fn get_bit(&self, pos: usize) -> Option<bool>;
}

/// An interface for accessing elements on integer arrays.
pub trait IntGetter {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    fn get_int(&self, pos: usize) -> Option<usize>;
}

/// An interface for rank operations on an ordered set of integers $`S \subseteq \{ 0,1,\dots,n-1 \}`$.
pub trait Ranker {
    /// Returns the cardinality of $`\{ x \mid x \in S, x < i \}`$, i.e.,
    /// the number of integers in $`S`$ that are no greater than `i`.
    fn rank1(&self, i: usize) -> Option<usize>;

    /// Returns the cardinality of $`\{ x \mid x \not\in S, 0 \leq x < i \}`$, i.e.,
    /// the number of integers not in $`S`$ that are no greater than `i`.
    fn rank0(&self, i: usize) -> Option<usize>;
}

/// An interface for select operations on an ordered set of integers $`S \subseteq \{ 0,1,\dots,n-1 \}`$.
pub trait Selector {
    /// Returns the position of the `k`-th smallest integer in $`S`$.
    fn select1(&self, k: usize) -> Option<usize>;

    /// Returns the position of the `k`-th smallest integer in $`S^{-1}`$,
    /// where $`S^{-1} = \{ 0,1,\dots,n-1 \} \setminus S`$.
    fn select0(&self, k: usize) -> Option<usize>;
}
