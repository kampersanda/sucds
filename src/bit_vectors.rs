//! Top module for bit vectors.
//!
//! # Introduction
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
//! - $`\textrm{Update}(i)`$ inserts/removes $`i`$ to/from $`S`$.
//!
//! Note that they are not limited depending on data structures.
//!
//! # Data structures
//!
//! Let $`n`$ be the number of positions (i.e., $`n = |S|`$).
//! The implementations provided in this crate are summarized below:
//!
//! | Implementations | [Access](BitGetter) | [Rank](Ranker) | [Select](Selector) | Update | Memory (bits) |
//! | --- | :-: | :-: | :-: | :-: | :-: |
//! | [`BitVector`] | $`O(1)`$  | $`O(u)`$ | $`O(u)`$ | $`O(1)`$ | $`u`$ |
//! | [`Rank9Sel`] | $`O(1)`$ | $`O(1)`$ | $`O(\lg u)`$ | -- | $`u + o(u)`$ |
//! | [`DArray`] | $`O(1)`$ | $`O(1)`$ | $`O(1)`$ | -- | $`u + o(u)`$ |
//! | [`SArray`] | $`O(\lg n)`$ | $`O(\lg \frac{u}{n})`$ | $`O(1)`$ | -- | $`n \lceil \lg \frac{u}{n} \rceil + 2n + o(n)`$ |
//!
//! ## Plain bit vectors without index
//!
//! [`BitVector`] is a plain format without index and the only mutable data structure.
//!
//! All search queries are performed by linear scan in $`O(u)`$ time,
//! although they are quickly computed in word units using bit-parallelism techniques.
//!
//! ## Plain bit vectors with index
//!
//! [`Rank9Sel`] and [`DArray`] are index structures for faster queries built on [`BitVector`].
//!
//! [`Rank9Sel`] is an implementation of Vigna's Rank9 and hinted selection techniques, supporting
//! constant-time Rank and logarithmic-time Select queries.
//!
//! [`DArray`] is a constant-time Select data structure by Okanohara and Sadakane.
//! If you need only Select queries on dense sets (i.e., $`n/u \approx 0.5`$), this will be the most candidate.
//! If your bit vector is a very sparse set (i.e., $`n \ll u`$), use [`SArray`] described below.
//! Rank/Predecessor/Successor queries are optionally enabled using the [`Rank9Sel`] index.
//! [`DArray`] outperforms [`Rank9Sel`] in complexity, but the practical space overhead of [`DArray`] can be larger.
//!
//! ## Very sparse bit vectors
//!
//! [`SArray`] is a data structure that allows us to store very sparse sets (i.e., $`n \ll u`$)
//! in compressed space, while supporting quick queries.
//! This is a specialized wrapper of [`EliasFano`](crate::mii_sequences::EliasFano).
pub mod bit_vector;
pub mod darray;
pub mod prelude;
pub mod rank9sel;
pub mod sarray;

pub use bit_vector::BitVector;
pub use darray::DArray;
pub use rank9sel::Rank9Sel;
pub use sarray::SArray;

use anyhow::Result;

/// Interface for building a bit vector with rank/select queries.
pub trait BitVectorBuilder {
    /// Creates a new vector from input bit stream `bits`.
    ///
    /// A data structure may not support a part of rank/select queries in the default
    /// configuration. The last three flags allow to enable them if optionally supported.
    ///
    /// # Arguments
    ///
    /// - `bits`: Bit stream.
    /// - `with_rank`: Flag to enable rank1/0.
    /// - `with_select1`: Flag to enable select1.
    /// - `with_select0`: Flag to enable select0.
    ///
    /// # Errors
    ///
    /// An error is returned if specified queries are not supported.
    fn build_from_bits<I>(
        bits: I,
        with_rank: bool,
        with_select1: bool,
        with_select0: bool,
    ) -> Result<Self>
    where
        I: IntoIterator<Item = bool>,
        Self: Sized;
}

/// Interface for reporting basic statistics in a bit vector.
pub trait BitVectorStat {
    /// Returns the number of bits stored.
    fn num_bits(&self) -> usize;

    /// Returns the number of bits set.
    fn num_ones(&self) -> usize;

    /// Returns the number of bits unset.
    #[inline(always)]
    fn num_zeros(&self) -> usize {
        self.num_bits() - self.num_ones()
    }
}

/// Interface for accessing elements on bit arrays.
pub trait BitGetter {
    /// Returns the `pos`-th bit, or [`None`] if out of bounds.
    fn get_bit(&self, pos: usize) -> Option<bool>;
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
