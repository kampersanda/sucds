//! # `sucds`: Succinct data structures in Rust
//!
//! `sucds` contains some succinct data structures written in Rust.
//!
//! ## Data structures
//!
//! So far, the following data structures are implemented. All of them are yet another Rust ports of implementations of [C++ Succinct library by Ottaviano](https://github.com/ot/succinct).
//!
//! - `BitVector`
//!   - Bit vector in a plain format, supporting some utilities such as update, chunking, and predecessor queries.
//! - `RsBitVector`
//!   - Rank/select data structure over bit vector through Vigna's rank9 and hinted selection techniques.
//! - `EliasFano`
//!   - Compressed monotone sequence through Elias-Fano encoding.
//! - `DArray`
//!   - Constant-time select data structure over integer set through dense array technique by Okanohara and Sadakane.
pub mod bit_vector;
pub mod broadword;
pub mod darray;
pub mod elias_fano;
pub mod intrinsics;
pub mod rs_bit_vector;

pub use bit_vector::BitVector;
pub use darray::DArray;
pub use elias_fano::EliasFano;
pub use elias_fano::EliasFanoBuilder;
pub use rs_bit_vector::RsBitVector;
