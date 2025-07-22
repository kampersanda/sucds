//! Top module for integer vectors.
//!
//! # Introduction
//!
//! Integer sequences consisting of many small values can be stored in compressed space
//! using *compressed integer vectors*.
//!
//! Let $`A = (a_0, a_1, \dots, a_{n-1})`$ be a sequence of $`n`$ unsigned integers.
//! Our integer vectors support the following queries:
//!
//! - $`\textrm{Access}(i)`$ returns $`a_i`$ (implemented by [`Access`]).
//! - $`\textrm{Update}(i, x)`$ modifies $`a_i \gets x`$.
//!
//! Note that they are not limited depending on data structures.
//!
//! # Data structures
//!
//! The implementations provided in this crate are summarized below:
//!
//! | Implementation | [Access](Access) | Update | Memory (bits) |
//! | --- | :-: | :-: | :-: |
//! | [`CompactVector`] | $`O(1)`$ | $`O(1)`$  | $`n \lceil \lg u \rceil`$ |
//! | [`PrefixSummedEliasFano`] | $`O(1)`$ | -- | $`n \lceil \lg \frac{N}{n} \rceil + 2n + o(n)`$ |
//! | [`DacsOpt`]  | $`O(\ell(a_i) / b)`$ | -- | $`\textrm{DAC}_\textrm{Opt}(A) + o(\textrm{DAC}_\textrm{Opt}(A)/b) + O(\lg u)`$ |
//! | [`DacsByte`] | $`O(\ell(a_i) / b)`$ | -- | $`\textrm{DAC}_\textrm{Byte}(A) + o(\textrm{DAC}_\textrm{Byte}(A)/b) + O(\lg u)`$ |
//!
//! The parameters are introduced below.
//!
//! ## Plain format without index
//!
//! [`CompactVector`] is a simple data structure in which each integer is represented in a fixed number of bits.
//! Assuming $`u`$ is the maximum value in $`A`$ plus 1,
//! each integer is stored in $`\lceil \lg u \rceil`$ bits of space.
//!
//! This is the only updatable data structure and will be the fastest due to its simplicity.
//! However, the compression performance is poor, especially when $`A`$ contains at least one large value.
//!
//! ## Compressed format with Elias-Fano encoding
//!
//! [`PrefixSummedEliasFano`] is a compressed data structure that stores the prefix-summed sequence from $`A`$
//! with the Elias-Fano encoding.
//! Assuming $`N`$ is the sum of values in $`A`$ plus 1 (i.e., $`N = 1 + \sum {a_i}`$),
//! the total memory is $`n \lceil \lg \frac{N}{n} \rceil + 2n + o(n)`$ in bits,
//! while supporting constant-time random access.
//!
//! ## Compressed format with Directly Addressable Codes
//!
//! [`DacsByte`] and [`DacsOpt`] are compressed data structures using Directly Addressable Codes (DACs),
//! which are randomly-accessible variants of the VByte encoding scheme.
//! [`DacsByte`] is a faster variant, and [`DacsOpt`] is a smaller variant.
//!
//! Let
//!
//!  - $`\ell(a)`$ be the length in bits of the binary representation of an integer $`a`$,
//!  - $`b`$ be the length in bits assigned for each level with DACs, and
//!  - $`\textrm{DAC}(A)`$ be the length in bits of the encoded sequence from $`A`$ with DACs.
//!
//! The complexities are as shown in the table.
//! (For simplicity, we assume all levels have the same bit length $`b`$.)
//!
//! # Examples
//!
//! This module provides several traits for essential behaviors,
//! allowing to compare our integer vectors as components in your data structures.
//! [`prelude`] allows you to import them easily.
//!
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use sucds::int_vectors::{DacsOpt, prelude::*};
//!
//! let seq = DacsOpt::build_from_slice(&[5, 0, 100000, 334])?;
//!
//! assert_eq!(seq.num_vals(), 4);
//!
//! assert_eq!(seq.access(3), Some(334));
//! assert_eq!(seq.access(4), None);
//! # Ok(())
//! # }
//! ```
pub mod compact_vector;
pub mod dacs_byte;
pub mod dacs_opt;
pub mod prefix_summed_elias_fano;
pub mod prelude;

pub use compact_vector::CompactVector;
pub use dacs_byte::DacsByte;
pub use dacs_opt::DacsOpt;
pub use prefix_summed_elias_fano::PrefixSummedEliasFano;

/// Interface for building integer vectors.
pub trait Build {
    /// Creates a new vector from a slice of integers `vals`.
    ///
    /// # Arguments
    ///
    ///  - `vals`: Slice of integers to be stored.
    ///
    fn build_from_slice<T>(vals: &[T]) -> Self
    where
        T: Into<u64> + Copy,
        Self: Sized;
}

/// Interface for reporting basic statistics of integer vectors.
pub trait NumVals {
    /// Returns the number of integers stored.
    fn num_vals(&self) -> usize;
}

/// Interface for accessing elements on integer vectors.
pub trait Access {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    fn access(&self, pos: usize) -> Option<usize>;
}
