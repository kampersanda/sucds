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
//! ### Integer arrays
//!
//! Integer arrays consisting of many small values can be stored in compressed space
//! using *compressed integer arrays*.
//!
//! Let $`A = (a_0, a_1, \dots, a_{n-1})`$ be an array of $`n`$ unsigned integers.
//! Our integer arrays support the following queries:
//!
//! - $`\textrm{Access}(i)`$ returns $`a_i`$ (implemented by [`IntGetter`]).
//! - $`\textrm{Update}(i, x)`$ modifies $`a_i \gets x`$.
//!
//! Note that they are not limited depending on the data structures.
//!
//! #### Summary
//!
//! The implementations provided in this crate are summarized below:
//!
//! | Implementation | [Access](IntGetter) | Update | Memory (bits) |
//! | --- | :-: | :-: | :-: |
//! | [`CompactVector`] | $`O(1)`$ | $`O(1)`$  | $`n \lceil \lg u \rceil`$ |
//! | [`PrefixSummedEliasFano`] | $`O(1)`$ | -- | $`n \lceil \lg \frac{N}{n} \rceil + 2n + o(n)`$ |
//! | [`DacsOpt`]  | $`O(\ell(a_i) / b)`$ | -- | $`\textrm{DAC}_\textrm{Opt}(A) + o(\textrm{DAC}_\textrm{Opt}(A)/b)`$ |
//! | [`DacsByte`] | $`O(\ell(a_i) / b)`$ | -- | $`\textrm{DAC}_\textrm{Byte}(A) + o(\textrm{DAC}_\textrm{Byte}(A)/b)`$ |
//!
//! The parameters are introduced below.
//!
//! #### Plain format without index
//!
//! [`CompactVector`] is a simple data structure in which each integer is represented in a fixed number of bits.
//! Assuming $`u`$ is the maximum value in $`A`$ plus 1,
//! each integer is stored in $`\lceil \lg u \rceil`$ bits of space.
//!
//! This is the only mutable data structure and will be the fastest due to its simplicity.
//! However, the compression performance is poor, especially when $`A`$ contains at least one large value.
//!
//! #### Compressed format with Elias-Fano encoding
//!
//! [`PrefixSummedEliasFano`] is a compressed data structure that stores the prefix-summed sequence from $`A`$
//! with the Elias-Fano encoding.
//! Assuming $`N`$ is the sum of values in $`A`$ plus 1 (i.e., $`N = 1 + \sum {a_i}`$),
//! the total memory is $`n \lceil \lg \frac{N}{n} \rceil + 2n + o(n)`$ in bits,
//! while supporting constant-time random access.
//!
//! #### Compressed format with Directly Addressable Codes
//!
//! [`DacsByte`] and [`DacsOpt`] are compressed data structures using Directly Addressable Codes (DACs),
//! which are randomly-accessible variants of the VByte encoding scheme.
//! [`DacsByte`] is a faster variant, and [`DacsOpt`] is a smaller variant.
//!
//! Let $`\ell(a)`$ be the length in bits of the binary representation of an integer $`a`$,
//! $`b`$ be the length in bits for each codeword by DACs, and
//! $`\textrm{DAC}(A)`$ be the length in bits of the sequence encoded from $`A`$ by DACs.
//! The complexities are as shown in the table.
//! (For simplicity, we assume all codewords have the same bit length.)
//!
//! A notable property is the access time depends on $`\ell(a_i)`$ for the target value $`a_i`$.
//! If values accessed are small, DACs will perform faster than [`PrefixSummedEliasFano`].
//!
//! ### Bit vectors
//!
//! Bit vectors and operations on them are fundamental to succinct data structures.
//!
//! Let $`S \subseteq \{ 0,1,\dots,u-1 \}`$ be a set of positions
//! at which bits are set in a bit vector of length $`u`$.
//! Our bit vectors support the following queries:
//!
//! - $`\textrm{Access}(i)`$ returns `true` if $`i \in S`$ or `false` otherwise (implemented by [`BitGetter`]).
//! - $`\textrm{Rank}(i)`$ returns the cardinality of $`\{ x \mid x \in S, x < i \}`$ (implemented by [`Ranker`]).
//! - $`\textrm{Select}(k)`$ returns the $`k`$-th smallest position in $`S`$ (implemented by [`Selector`]).
//! - $`\textrm{Predecessor}(i)`$ returns the largest position $`x \in S`$ such that $`x \leq i`$ (implemented by [`Predecessor`]).
//! - $`\textrm{Successor}(i)`$ returns the smallest position $`x \in S`$ such that $`i \leq x`$ (implemented by [`Successor`]).
//! - $`\textrm{Update}(i)`$ inserts/removes $`i`$ to/from $`S`$.
//!
//! Note that they are not limited depending on the data structures.
//!
//! #### Summary
//!
//! Let $`n`$ be the number of positions (i.e., $`n = |S|`$).
//! The implementations provided in this crate are summarized below:
//!
//! | Implementations | [Access](BitGetter) | [Rank](Ranker) | [Select](Selector) | [Pred](Predecessor)/[Succ](Successor) | Update | Memory (bits) |
//! | --- | :-: | :-: | :-: | :-: | :-: | :-: |
//! | [`BitVector`] | $`O(1)`$  | $`O(u)`$ | $`O(u)`$ | $`O(u)`$ | $`O(1)`$ | $`u`$ |
//! | [`RsBitVector`] | $`O(1)`$ | $`O(1)`$ | $`O(\lg u)`$ | $`O(\lg u)`$ | -- | $`u + o(u)`$ |
//! | [`DArray`] | -- | -- | $`O(1)`$ | -- | -- | $`u + o(u)`$ |
//! | [`EliasFano`] | $`O(1)`$ | $`O(\lg \frac{u}{n})`$ | $`O(1)`$ | $`O(\lg \frac{u}{n})`$ | -- | $`n \lceil \lg \frac{u}{n} \rceil + 2n + o(n)`$ |
//!
//! #### Plain bit vectors without index
//!
//! [`BitVector`] implements a bit vector in a plain format that supports some operations
//! such as update, predecessor/successor queries, and unary decoding.
//!
//! #### Plain bit vectors with index
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
//!
//! ### Monotone-increasing sequences
//!
//! ### Character sequences
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
mod intrinsics;
pub mod prefix_summed_elias_fano;
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
pub use prefix_summed_elias_fano::PrefixSummedEliasFano;
pub use rs_bit_vector::RsBitVector;
pub use serial::Searial;
pub use wavelet_matrix::WaveletMatrix;

// NOTE(kampersanda): We should not use `get()` because it has been already used in most std
// containers with different type annotations.

/// Interface for accessing elements on bit arrays.
pub trait BitGetter {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    fn get_bit(&self, pos: usize) -> Option<bool>;
}

/// Interface for accessing elements on integer arrays.
pub trait IntGetter {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    fn get_int(&self, pos: usize) -> Option<usize>;
}

/// Interface for rank queries on monotone-increasing integer sequences.
///
/// Let $`X = (x_0, x_1, \dots, x_{n-1})`$ be a sequence of $`n`$ integers
/// such that $`0 \leq x_0`$, $`x_i \leq x_{i+1}`$, and $`x_{n-1} < u`$ for a universe $`u`$.
pub trait Ranker {
    /// Returns the number of elements $`x_k \in X`$ such that $`x_k < x`$,
    /// or [`None`] if $`u < x`$.
    fn rank1(&self, x: usize) -> Option<usize>;

    /// Returns the number of integers $`x' \not\in X`$ such that $`0 \leq x' < x`$,
    /// or [`None`] if $`u < x`$.
    fn rank0(&self, x: usize) -> Option<usize>;
}

/// Interface for select queries on monotone-increasing integer sequences.
///
/// Let $`X = (x_0, x_1, \dots, x_{n-1})`$ be a sequence of $`n`$ integers
/// such that $`0 \leq x_0`$, $`x_i \leq x_{i+1}`$, and $`x_{n-1} < u`$ for a universe $`u`$.
pub trait Selector {
    /// Returns $`x_k`$, or [`None`] if $`n \leq k`$.
    fn select1(&self, k: usize) -> Option<usize>;

    /// Returns the $`k`$-th smallest integer $`x`$ such that $`x \not\in X`$ and $`0 \leq x < u`$, or
    /// [`None`] if out of bounds.
    fn select0(&self, k: usize) -> Option<usize>;
}

/// Interface for predecessor queries on monotone-increasing integer sequences.
///
/// Let $`X = (x_0, x_1, \dots, x_{n-1})`$ be a sequence of $`n`$ integers
/// such that $`0 \leq x_0`$, $`x_i \leq x_{i+1}`$, and $`x_{n-1} < u`$ for a universe $`u`$.
pub trait Predecessor {
    /// Returns the largest element $`x_k \in X`$ such that $`x_k \leq x`$, or
    /// [`None`] if not found or $`u \leq x`$.
    fn predecessor1(&self, x: usize) -> Option<usize>;

    /// Returns the largest integer $`x' \not\in X`$ such that $`0 \leq x' \leq x`$, or
    /// [`None`] if not found or $`u \leq x`$.
    fn predecessor0(&self, x: usize) -> Option<usize>;
}

/// Interface for successor queries on monotone-increasing integer sequences.
///
/// Let $`X = (x_0, x_1, \dots, x_{n-1})`$ be a sequence of $`n`$ integers
/// such that $`0 \leq x_0`$, $`x_i \leq x_{i+1}`$, and $`x_{n-1} < u`$ for a universe $`u`$.
pub trait Successor {
    /// Returns the smallest element $`x_k \in X`$ such that $`x \leq x_k`$, or
    /// [`None`] if not found or $`u \leq x`$.
    fn successor1(&self, x: usize) -> Option<usize>;

    /// Returns the smallest integer $`x_k \not\in X`$ such that $`x \leq x' < u`$, or
    /// [`None`] if not found or $`u \leq x`$.
    fn successor0(&self, x: usize) -> Option<usize>;
}
