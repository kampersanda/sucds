//! Error type for this crate.
#[cfg(not(feature = "std"))]
use alloc::string::String;
use core::fmt;

/// Error type for this crate.
///
/// Errors are categorized into several kinds so that callers can handle them
/// without parsing error messages. Each variant holds a human-readable message
/// describing the concrete violation.
///
/// To branch on or test for a specific failure, match on the variant rather
/// than on the message, which is not part of the stable API.
///
/// # Examples
///
/// ```
/// use sucds::{int_vectors::CompactVector, SucdsError};
///
/// let e = CompactVector::new(65).err().unwrap();
/// assert!(matches!(e, SucdsError::InvalidArgument(_)));
/// ```
#[derive(Debug)]
#[non_exhaustive]
pub enum SucdsError {
    /// An argument is out of the valid range or does not satisfy
    /// the condition required by the operation.
    InvalidArgument(String),

    /// A given position (or range) is out of the bounds of the data structure.
    OutOfBounds(String),

    /// The operation is not allowed for the current state of the data structure.
    InvalidState(String),

    /// The operation is not supported by the data structure.
    Unsupported(String),

    /// An I/O error occurred in serialization or deserialization.
    ///
    /// This variant is available only with the `std` feature.
    #[cfg(feature = "std")]
    Io(std::io::Error),
}

impl SucdsError {
    /// Creates [`SucdsError::InvalidArgument`] with a message.
    pub fn invalid_argument<S>(msg: S) -> Self
    where
        S: Into<String>,
    {
        Self::InvalidArgument(msg.into())
    }

    /// Creates [`SucdsError::OutOfBounds`] with a message.
    pub fn out_of_bounds<S>(msg: S) -> Self
    where
        S: Into<String>,
    {
        Self::OutOfBounds(msg.into())
    }

    /// Creates [`SucdsError::InvalidState`] with a message.
    pub fn invalid_state<S>(msg: S) -> Self
    where
        S: Into<String>,
    {
        Self::InvalidState(msg.into())
    }

    /// Creates [`SucdsError::Unsupported`] with a message.
    pub fn unsupported<S>(msg: S) -> Self
    where
        S: Into<String>,
    {
        Self::Unsupported(msg.into())
    }
}

impl fmt::Display for SucdsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidArgument(msg) => write!(f, "invalid argument: {msg}"),
            Self::OutOfBounds(msg) => write!(f, "out of bounds: {msg}"),
            Self::InvalidState(msg) => write!(f, "invalid state: {msg}"),
            Self::Unsupported(msg) => write!(f, "unsupported operation: {msg}"),
            #[cfg(feature = "std")]
            Self::Io(e) => write!(f, "io error: {e}"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for SucdsError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

#[cfg(feature = "std")]
impl From<std::io::Error> for SucdsError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}
