//! Utilities.
#![cfg(target_pointer_width = "64")]

pub mod int_io;
pub mod vec_io;

use crate::broadword;

/// Returns the number of bits to represent `x` at least.
///
/// # Example
///
/// ```
/// use sucds::util::needed_bits;
///
/// assert_eq!(needed_bits(0), 1);
/// assert_eq!(needed_bits(1), 1);
/// assert_eq!(needed_bits(2), 2);
/// assert_eq!(needed_bits(255), 8);
/// assert_eq!(needed_bits(256), 9);
/// ```
pub fn needed_bits(x: usize) -> usize {
    broadword::msb(x).map_or(1, |n| n + 1)
}
