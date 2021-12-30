//! # `sucds`: Succinct data structures in Rust
//!
//! `sucds` contains some [succinct data structures](https://en.wikipedia.org/wiki/Succinct_data_structure) written in Rust.
//!
//! ## Data structures
//!
//! So far, the following data structures are implemented. Most of them are yet another Rust ports of implementations of [C++ Succinct library by Ottaviano](https://github.com/ot/succinct).
//! For a detailed description of each data structure, please see the [respective documentation](https://docs.rs/sucds/latest/sucds/).
//!
//! - [`BitVector`]
//!   - Bit vector in a plain format, supporting some utilities such as update, chunking, and predecessor queries.
//! - [`CompactVector`]
//!   - Compact vector in which each integer is represented in the specified number of bits.
//! - [`RsBitVector`]
//!   - Rank/select data structure over bit vector through Vigna's rank9 and hinted selection techniques.
//! - [`DArray`]
//!   - Constant-time select data structure over integer set through dense array technique by Okanohara and Sadakane.
//! - [`EliasFano`]
//!   - Compressed monotone sequence through Elias-Fano encoding.
//! - [`EliasFanoList`]
//!   - Compressed integer list through Elias-Fano gap encoding.
pub mod bit_vector;
pub mod broadword;
pub mod compact_vector;
pub mod darray;
pub mod elias_fano;
pub mod elias_fano_list;
pub mod intrinsics;
pub mod rs_bit_vector;
pub mod util;

pub use bit_vector::BitVector;
pub use compact_vector::CompactVector;
pub use darray::DArray;
pub use elias_fano::EliasFano;
pub use elias_fano::EliasFanoBuilder;
pub use elias_fano_list::EliasFanoList;
pub use rs_bit_vector::RsBitVector;
