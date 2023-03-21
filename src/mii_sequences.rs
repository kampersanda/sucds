//! Top module for monotone-increasing integer sequences.
//!
//! # Introduction
//!
//! *Monotone-increasing integer sequences* are a generalization of bit vectors, a multiset variant of bit positions.
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
//! Note that they are not limited depending on the data structures.
//!
//! # Data structures
//!
//! The implementations provided in this crate are summarized below:
//!
//! | Implementations | [Rank](Ranker) | [Select](Selector) | [Pred](Predecessor)/[Succ](Successor) | Memory (bits) |
//! | --- | :-: | :-: | :-: | :-: |
//! | [`EliasFano`] | $`O(\lg \frac{u}{n})`$ | $`O(1)`$ | $`O(\lg \frac{u}{n})`$ | $`n \lceil \lg \frac{u}{n} \rceil + 2n + o(n)`$ |
//!
//! ## Elias-Fano encoding
//!
//! [`EliasFano`] is an efficient data structure for sparse sequences (i.e., $`n \ll u`$).
//! In addition to the basic queires listed above, this provides several access queries such as binary search.
pub mod elias_fano;
pub mod prelude;

pub use elias_fano::EliasFano;
pub use elias_fano::EliasFanoBuilder;

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
