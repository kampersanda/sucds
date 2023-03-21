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
//! - **Keep interface:**
//!   Sucds will follow a common interface to allow combining and replacing data structures.
//!
//! - **Keep identity:**
//!   Sucds does not aim to provide every succinct data structure, only those that are not competitive with others.
//!
//! - **Keep safety:**
//!   Sucds will not employ unsafe instructions used for very low-level programming.
//!
//! - **Keep Rust:**
//!   Sucds will stick to Pure Rust.
//!
//! ## Data structures
//!
//! We introduce the data structures provided in this crate, categorized as follows:
//!
//! 1. [Integer arrays](#integer-arrays)
//! 1. [Bit vectors](#bit-vectors)
//! 1. [Monotone-increasing integer sequences](#monotone-increasing-integer-sequences)
//! 1. [Character sequences](#character-sequences)
//!
//! In the description, we write $`\log_2`$ with $`\lg`$.
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
pub mod util;

pub use serial::Serializable;

// NOTE(kampersanda): We should not use `get()` because it has been already used in most std
// containers with different type annotations.
