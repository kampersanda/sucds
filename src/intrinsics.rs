#![cfg(target_pointer_width = "64")]
#![cfg(feature = "intrinsics")]

#[inline(always)]
pub const fn popcount(x: usize) -> usize {
    x.count_ones() as usize
}

#[inline(always)]
pub const fn bsf64(mask: usize) -> Option<usize> {
    if mask != 0 {
        Some(mask.trailing_zeros() as usize)
    } else {
        None
    }
}

#[inline(always)]
pub const fn bsr64(mask: usize) -> Option<usize> {
    if mask != 0 {
        Some(63 - mask.leading_zeros() as usize)
    } else {
        None
    }
}
