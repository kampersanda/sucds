//! # Succinct data structures in Rust
//!
//! Sucds is a collection of [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure),
//! powerful tools to store a variety of data structures in compressed space and
//! quickly perform operations on the compressed data.
//!
//! ## Design policy
//!
//! Thus far, many succinct data structures and their implementation techniques have been developed
//! for a wide range of applications.
//! To handle them in a single crate, we set up several design policies:
//!
//! - **Keep interface:**
//!   Sucds will follow a common interface to allow combining and replacing data structures.
//!
//! - **Keep identity:**
//!   Sucds does not aim to provide every succinct data structure, only those that are not competitive with others.
//!
//! - **Keep safety:**
//!   Sucds will not employ unsafe instructions used for very low-level programming.
//!
//! - **Keep Rust:**
//!   Sucds will stick to Pure Rust.
//!
//! ## Data structures
//!
//! We introduce the data structures provided in this crate, categorized as follows:
//!
//! 1. [Integer arrays](#integer-arrays)
//! 1. [Bit vectors](#bit-vectors)
//! 1. [Monotone-increasing integer sequences](#monotone-increasing-integer-sequences)
//! 1. [Character sequences](#character-sequences)
//!
//! In the description, we write $`\log_2`$ with $`\lg`$.
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
//! | [`DacsOpt`]  | $`O(\ell(a_i) / b)`$ | -- | $`\textrm{DAC}_\textrm{Opt}(A) + o(\textrm{DAC}_\textrm{Opt}(A)/b) + O(\lg u)`$ |
//! | [`DacsByte`] | $`O(\ell(a_i) / b)`$ | -- | $`\textrm{DAC}_\textrm{Byte}(A) + o(\textrm{DAC}_\textrm{Byte}(A)/b) + O(\lg u)`$ |
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
//! $`b`$ be the length in bits for each codeword with DACs, and
//! $`\textrm{DAC}(A)`$ be the length in bits of the encoded sequence from $`A`$ with DACs.
//! The complexities are as shown in the table.
//! (For simplicity, we assume all codewords have the same bit length $`b`$.)
//!
//! A notable property is the access time depends on $`\ell(a_i)`$ for the target value $`a_i`$.
//! If values accessed are small, DACs can perform faster than [`PrefixSummedEliasFano`]
//! due to the simplicity of the data structure.
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
//! - $`\textrm{Rank}(i)`$ returns the cardinality of $`\{ x \in S \mid x < i \}`$ (implemented by [`Ranker`]).
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
//! | [`EliasFano`] | -- | $`O(\lg \frac{u}{n})`$ | $`O(1)`$ | $`O(\lg \frac{u}{n})`$ | -- | $`n \lceil \lg \frac{u}{n} \rceil + 2n + o(n)`$ |
//!
//! #### Plain bit vectors without index
//!
//! [`BitVector`] is a plain format without index and the only mutable data structure.
//!
//! All search queries are performed by linear scan in $`O(u)`$ time,
//! although they are quickly computed in word units using bit-parallelism techniques.
//!
//! #### Plain bit vectors with index
//!
//! [`RsBitVector`] and [`DArray`] are index structures for faster queries built on [`BitVector`].
//!
//! [`RsBitVector`] is an implementation of Vigna's Rank9 and hinted selection techniques, supporting
//! constant-time Rank and logarithmic-time Select queries.
//!
//! [`DArray`] is a constant-time Select data structure by Okanohara and Sadakane.
//! If you need only Select queries on dense sets (i.e., $`n/u \approx 0.5`$),
//! this will be the most candidate.
//! If your bit vector is a very sparse set (i.e., $`n \ll u`$), use [`EliasFano`] described below.
//!
//! #### Very sparse bit vectors
//!
//! [`EliasFano`] is a data structure that allows us to store very sparse sets (i.e., $`n \ll u`$)
//! in compressed space, while supporting quick queries.
//! This data structure is also known as [*SArray*](https://arxiv.org/abs/cs/0610001).
//!
//! ### Monotone-increasing integer sequences
//!
//! *Monotone-increasing integer sequences* are a generalization of bit vectors, which are a multiset variant of $`S`$.
//! More simply, it is a sorted array of integers.
//!
//! Let $`X = (x_0, x_1, \dots, x_{n-1})`$ be a sequence of $`n`$ integers
//! such that $`0 \leq x_0`$, $`x_i \leq x_{i+1}`$, and $`x_{n-1} < u`$ for a universe $`u`$.
//! Our sequences support the following queries:
//!
//! - $`\textrm{Rank}(x)`$ returns the number of elements $`x_k \in X`$ such that $`x_k < x`$ (implemented by [`Ranker`]).
//! - $`\textrm{Select}(k)`$ returns $`x_k`$ (implemented by [`Selector`]).
//! - $`\textrm{Predecessor}(x)`$ returns the largest element $`x_k \in X`$ such that $`x_k \leq x`$ (implemented by [`Predecessor`]).
//! - $`\textrm{Successor}(x)`$ returns the smallest element $`x_k \in X`$ such that $`x \leq x_k`$ (implemented by [`Successor`]).
//!
//! [`EliasFano`] is applicable to monotone-increasing integer sequences in the same complexities as bit vectors.
//!
//! ### Character sequences
//!
//! *Character sequences* are another generalization of bit vectors,
//! whose elements are drawn from an alphabet $`\Sigma = \{ 0,1,\dots,\sigma - 1 \}`$.
//!
//! Let $`(c_0, c_1, \dots, c_{n-1}) \in \Sigma^{n} `$ be a sequence of $`n`$ characters.
//! Our sequences support the following queries:
//!
//! - $`\textrm{Access}(i)`$ returns $`c_i`$.
//! - $`\textrm{Rank}(i,c)`$ returns the number of occurrences of character $`c`$ for $`c_0,c_1,\dots,c_{i-1}`$.
//! - $`\textrm{Select}(k,c)`$ returns the occurrence position of the $`k`$-th character $`c`$.
//!
//! Note that they are not limited depending on the data structures.
//!
//! #### Summary
//!
//! The implementations provided in this crate are summarized below:
//!
//! | Implementation | Access | Rank | Select | Memory (bits) |
//! | --- | :-: | :-: | :-: | :-: |
//! | [`WaveletMatrix`] | $`O(\lg \sigma)`$ | $`O(\lg \sigma)`$ | $`O(\lg \sigma)`$ | $`n \lg \sigma + o (n \lg \sigma ) + O(\lg \sigma \lg n)`$ |
//!
//! Since there is only one implementation, we do not provide traits for the queries.
//!
//! #### Wavelet trees
//!
//! [`WaveletMatrix`] is a practical variant of Wavelet trees that are functional character sequences.
//! In addition to the basic queires listed above, this provides several range queries
//! such as [`quantile`](WaveletMatrix::quantile) or [`intersect`](WaveletMatrix::intersect).
//!
//! ## Serialization/deserialization
//!
//! All the data structures can be serialized or deserialized through the [`Searial`] trait.
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
