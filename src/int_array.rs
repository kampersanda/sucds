//! An interface for handling immutable integer arrays.

/// An interface for handling immutable integer arrays.
pub trait IntArray {
    /// Returns the `pos`-th integer.
    fn get(&self, pos: usize) -> usize;

    /// Returns the number of integers stored.
    fn len(&self) -> usize;

    /// Checks if the array is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl IntArray for Vec<usize> {
    #[inline(always)]
    fn get(&self, pos: usize) -> usize {
        (*self)[pos]
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.len()
    }
}

impl IntArray for [usize] {
    #[inline(always)]
    fn get(&self, pos: usize) -> usize {
        (*self)[pos]
    }

    #[inline(always)]
    fn len(&self) -> usize {
        self.len()
    }
}
