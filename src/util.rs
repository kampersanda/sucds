//! Utilities in Sucds.
#![cfg(target_pointer_width = "64")]

use crate::broadword;

/// Returns the number of bits to represent `x` at least.
///
/// # Examples
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

/// Returns `ceil(x / y)`.
///
/// # Examples
///
/// ```
/// use sucds::util::ceiled_divide;
///
/// assert_eq!(ceiled_divide(10, 2), 5);
/// assert_eq!(ceiled_divide(10, 3), 4);
/// ```
///
/// # Panics
///
/// It will panic if `y == 0`.
pub const fn ceiled_divide(x: usize, y: usize) -> usize {
    (x + y - 1) / y
}
