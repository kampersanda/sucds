//! The prelude for monotone-increasing integer sequences.
//!
//! The purpose of this module is to alleviate imports of many common traits for monotone-increasing integer sequences.
//!
//! ```
//! # #![allow(unused_imports)]
//! use sucds::mii_sequences::prelude::*;
//! ```
pub use crate::mii_sequences::{Predecessor, Ranker, Selector, Successor};
