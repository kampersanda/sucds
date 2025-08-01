//! Utilities in Sucds.
#![cfg(target_pointer_width = "64")]

use crate::broadword;

/// Returns the number of bits to represent `x` at least.
///
/// # Examples
///
/// ```
/// use sucds::utils::needed_bits;
///
/// assert_eq!(needed_bits(0), 1);
/// assert_eq!(needed_bits(1), 1);
/// assert_eq!(needed_bits(2), 2);
/// assert_eq!(needed_bits(255), 8);
/// assert_eq!(needed_bits(256), 9);
/// ```
pub fn needed_bits(x: u64) -> usize {
    broadword::msb(x).map_or(1, |n| n + 1)
}

/// Returns `ceil(x / y)`.
///
/// # Examples
///
/// ```
/// use sucds::utils::ceiled_divide;
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

/// A debug view of a matrix-like structure for long arrays.
pub(crate) struct MatrixView<'a, T> {
    data: &'a [T],
    cols: usize,
}

impl<'a, T> MatrixView<'a, T> {
    /// Creates a new `MatrixView` from a slice and the number of columns.
    ///
    /// # Arguments
    ///
    /// - `data`: A slice of data.
    /// - `cols`: The number of columns in the matrix.
    pub fn new(data: &'a [T], cols: usize) -> Self {
        assert!(cols > 0, "Number of columns must be greater than zero.");
        Self { data, cols }
    }
}

impl<'a, T: std::fmt::Debug> std::fmt::Debug for MatrixView<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Use the "pretty" format specifier '#' to decide whether to format nicely
        if f.alternate() {
            writeln!(f, "[")?;
            for row in self.data.chunks(self.cols) {
                write!(f, "    ")?;
                for (i, item) in row.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{item:?}")?;
                }
                writeln!(f, ",")?;
            }
            write!(f, "]")
        } else {
            // For a compact view (e.g., `{:?}`), just show a summary
            write!(f, "[{} items]", self.data.len())
        }
    }
}
