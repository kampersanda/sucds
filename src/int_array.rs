//! An interface for handling immutable integer arrays.

/// An interface for handling immutable integer arrays.
///
/// # Examples
///
/// ```
/// use sucds::IntArray;
///
/// let a = vec![1, 2, 3];
///
/// assert_eq!(a.get(0), 1);
/// assert_eq!(a.get(1), 2);
/// assert_eq!(a.get(2), 3);
///
/// assert_eq!(a.len(), 3);
/// ```
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
