//! Arrays of primitive integers that are owned or shared with serialized bytes.

use alloc::vec::Vec;
use core::mem::{align_of, size_of};
use core::ops::Deref;
use core::ptr::NonNull;

use bytes::Bytes;

use crate::io::{Read, Write};
use crate::serial::{padding_len, read_from_bytes, write_padding};
use crate::Result;
use crate::Serializable;
use crate::SucdsError;

/// Primitive integer types whose arrays can be viewed from little-endian bytes as they are.
///
/// # Safety
///
/// Every bit pattern must be a valid value of the type.
pub unsafe trait Pod: Serializable + Copy {}

unsafe impl Pod for u8 {}
unsafe impl Pod for u16 {}
unsafe impl Pod for u32 {}
unsafe impl Pod for u64 {}
unsafe impl Pod for i8 {}
unsafe impl Pod for i16 {}
unsafe impl Pod for i32 {}
unsafe impl Pod for i64 {}

/// Array of primitive integers that is owned or shared with serialized bytes.
///
/// The shared array is copied into an owned one when it is modified.
pub struct Storage<T> {
    // View of the array in `repr`, cached so that accesses need no branch.
    ptr: NonNull<T>,
    len: usize,
    repr: Repr<T>,
}

#[derive(Clone)]
enum Repr<T> {
    Owned(Vec<T>),
    /// Non-empty bytes aligned for `T` whose length is a multiple of `size_of::<T>()`.
    Shared(Bytes),
}

// SAFETY: `ptr` only points into `repr`, which is `Send` and `Sync` if `T` is.
unsafe impl<T: Send> Send for Storage<T> {}
unsafe impl<T: Sync> Sync for Storage<T> {}

impl<T> Storage<T> {
    fn new(repr: Repr<T>) -> Self {
        let (ptr, len) = match &repr {
            Repr::Owned(v) => (NonNull::from(&v[..]).cast(), v.len()),
            Repr::Shared(b) => (NonNull::from(&b[..]).cast(), b.len() / size_of::<T>()),
        };
        Self { ptr, len, repr }
    }
}

impl<T> Storage<T>
where
    T: Pod,
{
    /// Updates the vector with `f`, copying the shared array if any.
    #[inline(always)]
    pub fn update<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Vec<T>) -> R,
    {
        let mut v = core::mem::take(self).into_vec();
        let r = f(&mut v);
        *self = v.into();
        r
    }

    /// Converts into the vector, copying the shared array if any.
    pub fn into_vec(self) -> Vec<T> {
        match self.repr {
            Repr::Owned(v) => v,
            Repr::Shared(_) => self.to_vec(),
        }
    }

    /// Returns the number of elements it can hold without reallocating.
    pub fn capacity(&self) -> usize {
        match &self.repr {
            Repr::Owned(v) => v.capacity(),
            Repr::Shared(_) => self.len,
        }
    }

    /// Shrinks the capacity of the owned vector as much as possible.
    pub fn shrink_to_fit(&mut self) {
        if let Repr::Owned(_) = self.repr {
            self.update(Vec::shrink_to_fit);
        }
    }

    #[cfg(test)]
    pub const fn is_shared(&self) -> bool {
        matches!(self.repr, Repr::Shared(_))
    }
}

/// Serialized in the same format as [`Vec`].
impl<T> Serializable for Storage<T>
where
    T: Pod,
{
    fn serialize_into<W: Write>(&self, mut writer: W) -> Result<usize> {
        let mut mem = self.len().serialize_into(&mut writer)?;
        for x in self.iter() {
            mem += x.serialize_into(&mut writer)?;
        }
        mem += write_padding(&mut writer, mem)?;
        Ok(mem)
    }

    fn deserialize_from<R: Read>(reader: R) -> Result<Self> {
        Vec::<T>::deserialize_from(reader).map(Self::from)
    }

    /// Deserializes the array sharing `bytes`.
    ///
    /// The array is copied if `bytes` is not aligned for `T` or the machine is big-endian.
    ///
    /// # Complexity
    ///
    /// Constant time if shared, or linear in the length if copied.
    fn deserialize_from_bytes(bytes: &mut Bytes) -> Result<Self> {
        let len = read_from_bytes(bytes, |r| usize::deserialize_from(r))?;
        let size = len
            .checked_mul(size_of::<T>())
            .filter(|&size| size + padding_len(size) <= bytes.len())
            .ok_or_else(|| {
                SucdsError::invalid_data(format!(
                    "The array of {len} elements exceeds the remaining {} bytes.",
                    bytes.len()
                ))
            })?;
        let data = bytes.split_to(size);
        let _ = bytes.split_to(padding_len(size));
        if size != 0
            && cfg!(target_endian = "little")
            && data.as_ptr() as usize % align_of::<T>() == 0
        {
            Ok(Self::new(Repr::Shared(data)))
        } else {
            data.chunks_exact(size_of::<T>())
                .map(T::deserialize_from)
                .collect::<Result<Vec<_>>>()
                .map(Self::from)
        }
    }

    fn size_in_bytes(&self) -> usize {
        let size = T::size_of().unwrap() * self.len();
        usize::size_of().unwrap() + size + padding_len(size)
    }
}

impl<T> Deref for Storage<T>
where
    T: Pod,
{
    type Target = [T];

    #[inline(always)]
    fn deref(&self) -> &[T] {
        // SAFETY: `ptr` and `len` view the array in `repr`. For shared bytes, they are non-empty,
        // aligned for `T`, and of a length multiple of `size_of::<T>()` (checked in
        // `deserialize_from_bytes()`), and any bit pattern is valid for `T`.
        unsafe { core::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}

impl<T> Clone for Storage<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self::new(self.repr.clone())
    }
}

impl<T> Default for Storage<T> {
    fn default() -> Self {
        Vec::new().into()
    }
}

impl<T> From<Vec<T>> for Storage<T> {
    fn from(v: Vec<T>) -> Self {
        Self::new(Repr::Owned(v))
    }
}

impl<T> PartialEq for Storage<T>
where
    T: Pod + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self[..] == other[..]
    }
}

impl<T> Eq for Storage<T> where T: Pod + Eq {}

impl<T> core::fmt::Debug for Storage<T>
where
    T: Pod + core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self[..].fmt(f)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;

    /// Bytes aligned for `u64`.
    struct AlignedBytes(Vec<u64>);

    impl AsRef<[u8]> for AlignedBytes {
        fn as_ref(&self) -> &[u8] {
            // SAFETY: Any `u64` array can be viewed as bytes.
            unsafe { core::slice::from_raw_parts(self.0.as_ptr().cast(), self.0.len() * 8) }
        }
    }

    /// Copies `src` into bytes aligned for `u64`.
    pub fn aligned(src: &[u8]) -> Bytes {
        let words = src
            .chunks(8)
            .map(|c| {
                let mut buf = [0; 8];
                buf[..c.len()].copy_from_slice(c);
                u64::from_ne_bytes(buf)
            })
            .collect();
        let bytes = Bytes::from_owner(AlignedBytes(words));
        bytes.slice(..src.len())
    }

    fn serialized(vals: &[u64]) -> Vec<u8> {
        let mut bytes = vec![];
        Storage::from(vals.to_vec())
            .serialize_into(&mut bytes)
            .unwrap();
        bytes
    }

    #[test]
    fn test_shared() {
        let mut bytes = aligned(&serialized(&[1, 2, 3]));
        let s = Storage::<u64>::deserialize_from_bytes(&mut bytes).unwrap();
        assert!(cfg!(target_endian = "big") || s.is_shared());
        assert_eq!(&s[..], &[1, 2, 3]);
        assert!(bytes.is_empty());
    }

    #[test]
    fn test_unaligned_copied() {
        // Shifted by one byte, which is unaligned for `u64` on any machine.
        let mut src = vec![0; 1];
        src.extend(serialized(&[1, 2, 3]));
        let mut bytes = aligned(&src);
        let _ = bytes.split_to(1);
        let s = Storage::<u64>::deserialize_from_bytes(&mut bytes).unwrap();
        assert!(!s.is_shared());
        assert_eq!(&s[..], &[1, 2, 3]);
        assert!(bytes.is_empty());
    }

    #[test]
    fn test_update() {
        let mut bytes = aligned(&serialized(&[1, 2, 3]));
        let mut s = Storage::<u64>::deserialize_from_bytes(&mut bytes).unwrap();
        s.update(|v| v[0] = 4);
        assert!(!s.is_shared());
        assert_eq!(&s[..], &[4, 2, 3]);
    }

    #[test]
    fn test_too_short() {
        let mut bytes = aligned(&serialized(&[1, 2, 3])).slice(..16);
        let e = Storage::<u64>::deserialize_from_bytes(&mut bytes);
        assert!(matches!(e, Err(SucdsError::InvalidData(_))));
    }
}
