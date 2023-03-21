//!
pub mod compact_vector;
pub mod dacs_byte;
pub mod dacs_opt;
pub mod prefix_summed_elias_fano;

pub use compact_vector::CompactVector;
pub use dacs_byte::DacsByte;
pub use dacs_opt::DacsOpt;
pub use prefix_summed_elias_fano::PrefixSummedEliasFano;

/// Interface for accessing elements on integer arrays.
pub trait IntGetter {
    /// Returns the `pos`-th integer, or [`None`] if out of bounds.
    fn get_int(&self, pos: usize) -> Option<usize>;
}
