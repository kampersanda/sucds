//! Top module for monotone-increasing integer sequences.
//!
//! # Introduction
//!
//! *Monotone-increasing integer sequences* are a generalization of [`bit_vectors`](crate::bit_vectors),
//! a multiset variant of bit positions.
//! More simply, it is a sorted array of integers.
//!
//! Let $`X = (x_0, x_1, \dots, x_{n-1})`$ be a sequence of $`n`$ integers
//! such that $`0 \leq x_0`$, $`x_i \leq x_{i+1}`$, and $`x_{n-1} < u`$ for a universe $`u`$.
//! Our sequences support the following queries:
//!
//! - $`\textrm{Rank}(x)`$ returns the number of elements $`x_k \in X`$ such that $`x_k < x`$.
//! - $`\textrm{Select}(k)`$ returns $`x_k`$.
//! - $`\textrm{Predecessor}(x)`$ returns the largest element $`x_k \in X`$ such that $`x_k \leq x`$.
//! - $`\textrm{Successor}(x)`$ returns the smallest element $`x_k \in X`$ such that $`x \leq x_k`$.
//!
//! Note that they are not limited depending on data structures.
//!
//! # Data structures
//!
//! The implementations provided in this crate are summarized below:
//!
//! | Implementations | Rank | Select | Pred/Succ | Memory (bits) |
//! | --- | :-: | :-: | :-: | :-: |
//! | [`EliasFano`] | $`O(\lg \frac{u}{n})`$ | $`O(1)`$ | $`O(\lg \frac{u}{n})`$ | $`n \lceil \lg \frac{u}{n} \rceil + 2n + o(n)`$ |
//!
//! Since there is only one implementation, we do not provide traits for the queries.
//!
//! ## Elias-Fano encoding
//!
//! [`EliasFano`] is an efficient data structure for sparse sequences (i.e., $`n \ll u`$).
//! In addition to the basic queires listed above, this provides several access queries such as binary search.
pub mod elias_fano;

pub use elias_fano::EliasFano;
pub use elias_fano::EliasFanoBuilder;
