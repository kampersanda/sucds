//! The module for bit vectors.
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

pub use crate::mii_sequences::Ranker;
pub use crate::mii_sequences::Selector;
