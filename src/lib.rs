//! # Succinct data structures in Rust
//!
//! Sucds is a collection of [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure),
//! powerful tools to store a variety of data structures in compressed space and
//! quickly perform operations on the compressed data.
//!
//! ## Data structures
//!
//! The current version supports the following data structures.
//!
//! [Navarro's textbook](https://users.dcc.uchile.cl/~gnavarro/CDSbook/).
//!
//!
//! ### Integer arrays
//!
//! Integer arrays consisting of small values can be stored in compressed space
//! using *compressed integer arrays*.
//! This crate provides the following variants:
//!
//! - [`CompactVector`]: Compact vector in which each integer is represented in a fixed number of bits.
//! - [`EliasFanoList`]: Compressed integer list with prefix-summed Elias-Fano encoding.
//! - [`DacsOpt`]: Compressed integer array using Directly Addressable Codes (DACs) with optimal assignment.
//! - [`DacsByte`]: Compressed integer array using Directly Addressable Codes (DACs) in a simple bytewise scheme.
//!
//! Let $`A = (a_0, a_1, \dots, a_{n-1})`$ be
//!
//! - $`\textrm{Access}(i)`$ returns $`a_i`$ (implemented for [`IntGetter`]).
//! - $`\textrm{Update}(i)`$ modifies $`a_i`$.
//!
//! #### Summary
//!
//! | Implementation | [Access](IntGetter) | Update | Space (bits) |
//! | --- | :-: | :-: | :-: |
//! | [`CompactVector`] | $`O(1)`$ | $`O(1)`$  | $`n \lceil \lg u \rceil`$ |
//! | [`EliasFanoList`] | $`O(1)`$ | -- | $`n \lceil \lg \frac{N}{n} \rceil + 2n + o(n)`$ |
//! | [`DacsOpt`] | $`O(\ell_i / b)`$ | -- |   |
//! | [`DacsByte`] | $`O(\ell_i / b)`$ | -- |   |
//!
//! ### Bit vectors
//!
//! Bit vectors and operations on them are fundamental to succinct data structures.
//!
//! [`BitVector`] implements a bit vector in a plain format that supports some operations
//! such as update, predecessor/successor queries, and unary decoding.
//!
//! Let $`S \subseteq \{ 0,1,\dots,n-1 \}`$ be a set of positions
//! at which bits are set in a bit vector of length $`n`$.
//!
//! - $`\textrm{Access}(i)`$ returns `true` if $`i \in S`$ or `false` otherwise (implemented for [`BitGetter`]).
//! - $`\textrm{Rank}(i)`$ returns the cardinality of $`\{ x \mid x \in S, x < i \}`$,
//!   i.e., the number of integers in $`S`$ that are less than `i` (implemented for [`Ranker`]).
//! - $`\textrm{Select}(k)`$ returns the position of the `k`-th smallest integer in $`S`$ (implemented for [`Selector`]).
//! - $`\textrm{Predecessor}(i)`$ returns
//! - $`\textrm{Successor}(i)`$ returns
//! - $`\textrm{Update}(i)`$ inserts/removes $`i`$ to/from $`S`$.
//!
//!
//! #### Rank/select queries
//!
//! *Rank/select queries* over bit vectors are core.
//! Traits [`Ranker`] and [`Selector`] implement the operations.
//!
//!  - [`RsBitVector`]: Vigna's rank/select data structure built on [`BitVector`],
//!    supporting constant-time rank and logarithmic-time select queries
//!  - [`DArray`]: Constant-time select data structure by Okanohara and Sadakane
//!
//! #### Very sparse bit vectors
//!
//! [`EliasFano`] is a compressed representation for monotone-increasing sequences, or multisets of integers.
//! Especially for sparse sequences, the representation can be very compact.
//! Another attraction of Elias-Fano is a set of powerful search queries on the compressed representation,
//! such as random access, binary searches, or rank/predecessor/successor queries.
//!
//! #### Summary
//!
//! | Implementation | [Access](BitGetter) | [Rank](Ranker) | [Select](Selector) | Pred/Succ | Update | Space (bits) |
//! | --- | :-: | :-: | :-: | :-: | :-: | :-: |
//! | [`BitVector`] | $`O(1)`$  | -- | -- | $`O(n)`$ | $`O(1)`$ | $`n`$ |
//! | [`RsBitVector`] | $`O(1)`$ | $`O(1)`$ | $`O(\lg n)`$ | $`O(\lg n)`$ | -- | $`n + o(n)`$ |
//! | [`DArray`] | -- | -- | $`O(1)`$ | -- | -- | $`n + o(n)`$ |
//! | [`EliasFano`] | $`O(1)`$ | $`O(\lg \frac{u}{n})`$ | $`O(1)`$ | $`O(\lg \frac{u}{n})`$ | -- | $`n \lceil \lg \frac{u}{n} \rceil + 2n + o(n)`$ |
//!
//! ### Monotone-increasing sequences
//!
//! ### Sequences
//!
//! [`WaveletMatrix`]
//!
//! ## Serialization/deserialization
//!
//! All the data structures
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

// NOTE(kampersanda): We should not use `get()` because it has been already used in most std
// containers with different type annotations.

/// An interface for accessing elements on integer arrays.
pub trait IntGetter {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    fn get_int(&self, pos: usize) -> Option<usize>;
}

/// An interface for accessing elements on bit arrays.
pub trait BitGetter {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    fn get_bit(&self, pos: usize) -> Option<bool>;
}

/// An interface for rank operations on an ordered set of integers $`S \subseteq \{ 0,1,\dots,n-1 \}`$.
pub trait Ranker {
    /// Returns the cardinality of $`\{ x \mid x \in S, x < i \}`$, i.e.,
    /// the number of integers in $`S`$ that are less than `i`.
    fn rank1(&self, i: usize) -> Option<usize>;

    /// Returns the cardinality of $`\{ x \mid x \not\in S, 0 \leq x < i \}`$, i.e.,
    /// the number of integers not in $`S`$ that are less than `i`.
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
