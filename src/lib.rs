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
//! - **Curated collection:** Rather than offering every possible succinct data structure,
//!   only those with competitive advantages are provided.
//! - **Consistent interfaces:** Data structures in the same category share traits
//!   such as `Access`, `Rank`, and `Select`, and are easily replaceable.
//! - **Ensured safety:** Unsafe instructions, typically reserved for extremely low-level
//!   programming, are avoided.
//! - **Pure Rust:** The implementation is written in pure Rust, with optional `no_std` support.
//!
//! ## Data structures
//!
//! The data structures provided in this crate are categorized as follows:
//!
//! - [Integer vectors](crate::int_vectors)
//! - [Bit vectors](crate::bit_vectors)
//! - [Monotone-increasing integer sequences](crate::mii_sequences)
//! - [Character sequences](crate::char_sequences)
//!
//! The descriptions for each category are available in the corresponding module.
//!
//! Throughout this document, we write $`\log_2`$ with $`\lg`$.
//!
//! ## Serialization/deserialization
//!
//! All the data structures can be serialized or deserialized through the `Serializable` trait,
//! which is defined on the [`Read`](crate::io::Read) and [`Write`](crate::io::Write) traits
//! in the [`io`] module.
//! With the `std` feature (enabled by default), those traits are re-exports of `std::io`,
//! and any reader or writer of the standard library can be used as usual.
//!
//! ### Memory-mapped files
//!
//! Data structures can also be deserialized from [`serial::Bytes`] without copying their arrays,
//! through [`Serializable::deserialize_from_bytes()`] and
//! [`Serializable::deserialize_from_bytes_unchecked()`].
//! With [`Bytes::from_owner()`](serial::Bytes::from_owner), the bytes can be a memory-mapped file
//! (e.g., `memmap2::Mmap`), which the deserialized data structure keeps alive.
//! The unchecked variant loads the data in constant time, skipping the consistency checks
//! that scan the whole data.
//!
//! Note that:
//!
//! - The file must not be modified or truncated while mapped; otherwise, the behavior is undefined.
//! - The arrays are shared only if the bytes start at an 8-byte boundary, which memory maps satisfy,
//!   and the machine is little-endian. Otherwise, they are copied.
//! - Queries on a data structure from the unchecked variant may panic if the file is corrupted.
//! - Modifying a loaded data structure (e.g., [`BitVector::set_bit()`](bit_vectors::BitVector::set_bit))
//!   copies its arrays into the heap.
//!
//! ## `no_std` support
//!
//! This crate supports `no_std` environments by disabling the default `std` feature,
//! although the `alloc` crate is always required.
//! Two things differ from the default build:
//!
//! - Readers and writers are limited to the byte containers available in `alloc`,
//!   i.e., [`Vec<u8>`](alloc::vec::Vec) and `&mut [u8]` for writing and `&[u8]` for reading.
//! - [`SucdsError`] does not implement `std::error::Error`, and its `Io` variant holds
//!   [`io::Error`] defined in this crate instead of `std::io::Error`.
//!
//! ## `intrinsics` feature
//!
//! Primitive bit operations in the [`broadword`] module are implemented with broadword
//! techniques by default.
//! Enabling the `intrinsics` feature replaces them with the equivalent operations of
//! the standard library, which can be compiled into dedicated CPU instructions.
//! Building with `RUSTFLAGS="-C target-cpu=native"` is recommended in that case.
//!
//! ## Portability
//!
//! This library is tuned for 64-bit machines but also runs on 32-bit ones, where
//! the broadword operations are emulated and each data structure holds less than
//! $`2^{32}`$ bits or integers.
//!
//! The serialization format is independent of the pointer width, since [`usize`]
//! and [`isize`] are stored as 64-bit little-endian integers. Deserialization fails
//! with [`SucdsError::InvalidArgument`] if a stored value does not fit in [`usize`]
//! of the machine.
#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
extern crate alloc;

/// Tests the code examples in README.md.
#[cfg(all(doctest, feature = "std"))]
#[doc = include_str!("../README.md")]
pub struct ReadmeDoctests;

pub mod bit_vectors;
pub mod broadword;
pub mod char_sequences;
pub mod errors;
pub mod int_vectors;
mod intrinsics;
pub mod io;
pub mod mii_sequences;
pub mod serial;
mod storage;
pub mod utils;

pub use errors::SucdsError;
pub use serial::Serializable;

/// Result type for this crate.
///
/// The error type is [`SucdsError`], defined in this crate.
pub type Result<T> = core::result::Result<T, SucdsError>;

// NOTE(kampersanda): We should not use `get()` because it has been already used in most std
// containers with different type annotations.
