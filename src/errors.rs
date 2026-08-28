//! Error type for this crate.
#[cfg(not(feature = "std"))]
use alloc::string::String;
use core::fmt;

/// Kind of [`SucdsError`].
///
/// This mirrors the variants of [`SucdsError`] without carrying a message, so
/// that errors can be compared and matched without depending on message text.
/// Obtain it with [`SucdsError::kind`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SucdsErrorKind {
    /// Kind of [`SucdsError::InvalidArgument`].
    InvalidArgument,

    /// Kind of [`SucdsError::OutOfBounds`].
    OutOfBounds,

    /// Kind of [`SucdsError::InvalidState`].
    InvalidState,

    /// Kind of [`SucdsError::Unsupported`].
    Unsupported,

    /// Kind of `SucdsError::Io`.
    ///
    /// This variant is available only with the `std` feature.
    #[cfg(feature = "std")]
    Io,
}

impl fmt::Display for SucdsErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::InvalidArgument => "invalid argument",
            Self::OutOfBounds => "out of bounds",
            Self::InvalidState => "invalid state",
            Self::Unsupported => "unsupported operation",
            #[cfg(feature = "std")]
            Self::Io => "io error",
        };
        f.write_str(s)
    }
}

/// Error type for this crate.
///
/// Errors are categorized into several kinds so that callers can handle them
/// without parsing error messages. Each variant holds a human-readable message
/// describing the concrete violation.
///
/// To branch on or compare errors, use [`SucdsError::kind`] rather than the
/// message, which is not part of the stable API.
///
/// This type derives only [`Debug`]: `Io` wraps `std::io::Error`, which
/// implements neither [`PartialEq`] nor [`Clone`]. Use [`SucdsErrorKind`],
/// which derives both, for comparisons.
///
/// # Examples
///
/// ```
/// use sucds::{int_vectors::CompactVector, SucdsErrorKind};
///
/// let e = CompactVector::new(65).err().unwrap();
/// assert_eq!(e.kind(), SucdsErrorKind::InvalidArgument);
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
    /// Returns the [`SucdsErrorKind`] of this error.
    ///
    /// Prefer this over inspecting the message when handling or testing errors.
    pub const fn kind(&self) -> SucdsErrorKind {
        match self {
            Self::InvalidArgument(_) => SucdsErrorKind::InvalidArgument,
            Self::OutOfBounds(_) => SucdsErrorKind::OutOfBounds,
            Self::InvalidState(_) => SucdsErrorKind::InvalidState,
            Self::Unsupported(_) => SucdsErrorKind::Unsupported,
            #[cfg(feature = "std")]
            Self::Io(_) => SucdsErrorKind::Io,
        }
    }

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
            Self::InvalidArgument(msg)
            | Self::OutOfBounds(msg)
            | Self::InvalidState(msg)
            | Self::Unsupported(msg) => write!(f, "{}: {msg}", self.kind()),
            #[cfg(feature = "std")]
            Self::Io(e) => write!(f, "{}: {e}", self.kind()),
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
