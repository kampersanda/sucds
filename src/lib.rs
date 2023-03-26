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
//! - **Maintain interface consistency:**
//!   Sucds will adhere to a unified interface, facilitating the integration and replacement of data structures.
//!
//! - **Preserve identity:**
//!   Rather than offering every possible succinct data structure,
//!   Sucds will focus on providing only those that hold a competitive advantage over others.
//!
//! - **Ensure safety:**
//!   To avoid potential risks, Sucds will refrain from using unsafe instructions
//!   typically reserved for extremely low-level programming.
//!
//! - **Remain Rust-centric:**
//!   Sucds will consistently utilize Pure Rust in its implementation.
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
//! All the data structures can be serialized or deserialized through the [`Serializable`] trait.
//!
//! ## Limitation
//!
//! This library is designed to run on 64-bit machines.
#![deny(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("`target_pointer_width` must be 64");

pub mod bit_vectors;
pub mod broadword;
pub mod char_sequences;
pub mod int_vectors;
mod intrinsics;
pub mod mii_sequences;
pub mod serial;
pub mod utils;

pub use serial::Serializable;

// NOTE(kampersanda): We should not use `get()` because it has been already used in most std
// containers with different type annotations.
