#![cfg(target_pointer_width = "64")]

use crate::broadword;

/// Returns the number of bits to represent `x` at least.
pub fn needed_bits(x: usize) -> usize {
    broadword::msb(x).map_or(1, |n| n + 1)
}
