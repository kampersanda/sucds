//! Minimal I/O abstraction for serialization.
//!
//! [`Serializable`](crate::Serializable) is defined on the [`Read`] and [`Write`] traits
//! in this module so that serialization works in `no_std` environments as well.
//!
//! With the `std` feature (enabled by default), the items in this module are simply
//! re-exports of `std::io`, and any reader or writer of the standard library can be used.
//! Without the feature, they are minimal replacements offering only the operations
//! serialization needs, implemented for the byte containers available in `alloc`,
//! i.e., [`Vec<u8>`](alloc::vec::Vec) and `&mut [u8]` for writing and `&[u8]` for reading.

#[cfg(feature = "std")]
pub use std::io::{Error, Read, Result, Write};

#[cfg(not(feature = "std"))]
pub use self::no_std::{Error, Read, Result, Write};

#[cfg(not(feature = "std"))]
mod no_std {
    use alloc::vec::Vec;
    use core::fmt;

    /// Error type for I/O operations in serialization.
    ///
    /// This is a minimal replacement for `std::io::Error` in `no_std` environments.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Error {
        /// A reader reached its end before the requested bytes were filled.
        UnexpectedEof,

        /// A writer could not accept the whole buffer.
        WriteZero,
    }

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Self::UnexpectedEof => write!(f, "failed to fill whole buffer"),
                Self::WriteZero => write!(f, "failed to write whole buffer"),
            }
        }
    }

    /// Result type for I/O operations in serialization.
    ///
    /// The error type is [`Error`], defined in this module.
    pub type Result<T> = core::result::Result<T, Error>;

    /// Trait to write bytes into a sink.
    ///
    /// This is a minimal replacement for `std::io::Write` in `no_std` environments.
    pub trait Write {
        /// Writes the entire buffer into this writer.
        ///
        /// # Arguments
        ///
        /// - `buf`: Bytes to be written.
        ///
        /// # Errors
        ///
        /// An error is returned if the writer cannot accept the whole buffer.
        fn write_all(&mut self, buf: &[u8]) -> Result<()>;
    }

    /// Trait to read bytes from a source.
    ///
    /// This is a minimal replacement for `std::io::Read` in `no_std` environments.
    pub trait Read {
        /// Reads the exact number of bytes required to fill the buffer.
        ///
        /// # Arguments
        ///
        /// - `buf`: Buffer to be filled.
        ///
        /// # Errors
        ///
        /// An error is returned if the reader ends before the buffer is filled.
        fn read_exact(&mut self, buf: &mut [u8]) -> Result<()>;
    }

    impl<W> Write for &mut W
    where
        W: Write + ?Sized,
    {
        fn write_all(&mut self, buf: &[u8]) -> Result<()> {
            (**self).write_all(buf)
        }
    }

    impl<R> Read for &mut R
    where
        R: Read + ?Sized,
    {
        fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
            (**self).read_exact(buf)
        }
    }

    impl Write for Vec<u8> {
        fn write_all(&mut self, buf: &[u8]) -> Result<()> {
            self.extend_from_slice(buf);
            Ok(())
        }
    }

    impl Write for &mut [u8] {
        fn write_all(&mut self, buf: &[u8]) -> Result<()> {
            if self.len() < buf.len() {
                return Err(Error::WriteZero);
            }
            let (dst, rest) = core::mem::take(self).split_at_mut(buf.len());
            dst.copy_from_slice(buf);
            *self = rest;
            Ok(())
        }
    }

    impl Read for &[u8] {
        fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
            if self.len() < buf.len() {
                return Err(Error::UnexpectedEof);
            }
            let (src, rest) = self.split_at(buf.len());
            buf.copy_from_slice(src);
            *self = rest;
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec_write_and_slice_read() {
        let mut writer = vec![];
        writer.write_all(&[1, 2, 3]).unwrap();
        writer.write_all(&[4, 5]).unwrap();
        assert_eq!(writer, vec![1, 2, 3, 4, 5]);

        let mut reader = &writer[..];
        let mut buf = [0; 3];
        reader.read_exact(&mut buf).unwrap();
        assert_eq!(buf, [1, 2, 3]);
        let mut buf = [0; 2];
        reader.read_exact(&mut buf).unwrap();
        assert_eq!(buf, [4, 5]);
    }

    #[test]
    fn test_slice_read_eof() {
        let bytes = [1, 2, 3];
        let mut reader = &bytes[..];
        let mut buf = [0; 4];
        assert!(reader.read_exact(&mut buf).is_err());
    }

    #[cfg(not(feature = "std"))]
    #[test]
    fn test_mut_slice_write() {
        let mut bytes = [0; 4];
        let mut writer = &mut bytes[..];
        writer.write_all(&[1, 2]).unwrap();
        writer.write_all(&[3, 4]).unwrap();
        assert_eq!(bytes, [1, 2, 3, 4]);
    }

    #[cfg(not(feature = "std"))]
    #[test]
    fn test_mut_slice_write_zero() {
        let mut bytes = [0; 2];
        let mut writer = &mut bytes[..];
        assert!(writer.write_all(&[1, 2, 3]).is_err());
    }
}
