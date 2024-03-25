// SPDX-License-Identifier: GPL-2.0

//! Extensions to [`Vec`] for fallible allocations.

use super::Flags;
use alloc::{alloc::AllocError, vec::Vec};
use core::{mem::ManuallyDrop, result::Result};

/// Extensions to [`Vec`].
pub trait VecExt<T>: Sized {
    /// Creates a new [`Vec`] instance with at least the given capacity.
    fn with_capacity(capacity: usize, flags: Flags) -> Result<Self, AllocError>;

    /// Appends an element to the back of the [`Vec`] instance.
    fn push(&mut self, v: T, flags: Flags) -> Result<(), AllocError>;

    /// Pushes clones of the elements of slice into the [`Vec`] instance.
    fn extend_from_slice(&mut self, other: &[T], flags: Flags) -> Result<(), AllocError>
    where
        T: Clone;

    /// Ensures that the capacity exceeds the length by at least `additional` elements.
    fn reserve(&mut self, additional: usize, flags: Flags) -> Result<(), AllocError>;
}

impl<T> VecExt<T> for Vec<T> {
    fn with_capacity(capacity: usize, flags: Flags) -> Result<Self, AllocError> {
        let mut v = Vec::new();
        <Self as VecExt<_>>::reserve(&mut v, capacity, flags)?;
        Ok(v)
    }

    fn push(&mut self, v: T, flags: Flags) -> Result<(), AllocError> {
        <Self as VecExt<_>>::reserve(self, 1, flags)?;
        let (ptr, len, cap) = destructure(self);
        // SAFETY: ptr is valid for `cap` elements. And `cap` is greater (by at least 1) than
        // `len` because of the call to `reserve` above. So the pointer after offsetting by `len`
        // elements is valid for write.
        unsafe { ptr.wrapping_add(len).write(v) };

        // SAFETY: The only difference from the values returned by `destructure` is that `length`
        // is incremented by 1, which is fine because we have just initialised the element at
        // offset `length`.
        unsafe { rebuild(self, ptr, len + 1, cap) };
        Ok(())
    }

    fn extend_from_slice(&mut self, other: &[T], flags: Flags) -> Result<(), AllocError>
    where
        T: Clone,
    {
        <Self as VecExt<_>>::reserve(self, other.len(), flags)?;
        for item in other {
            <Self as VecExt<_>>::push(self, item.clone(), flags)?;
        }
        Ok(())
    }

    #[cfg(any(test, testlib))]
    fn reserve(&mut self, additional: usize, _flags: Flags) -> Result<(), AllocError> {
        Vec::reserve(self, additional);
        Ok(())
    }

    #[cfg(not(any(test, testlib)))]
    fn reserve(&mut self, additional: usize, flags: Flags) -> Result<(), AllocError> {
        let len = self.len();
        let cap = self.capacity();

        if cap - len >= additional {
            return Ok(());
        }

        if core::mem::size_of::<T>() == 0 {
            // The capacity is already `usize::MAX` for SZTs, we can't go higher.
            return Err(AllocError);
        }

        // We know cap is <= `isize::MAX` because `Layout::array` fails if the resulting byte size
        // is greater than `isize::MAX`. So the multiplication by two won't overflow.
        let new_cap = core::cmp::max(cap * 2, len.checked_add(additional).ok_or(AllocError)?);
        let layout = core::alloc::Layout::array::<T>(new_cap).map_err(|_| AllocError)?;

        let (ptr, len, cap) = destructure(self);

        // SAFETY: `ptr` is valid because it's either NULL or comes from a previous call to
        // `krealloc_aligned`. We also verified that the type is not a ZST.
        let new_ptr = unsafe { super::allocator::krealloc_aligned(ptr.cast(), layout, flags.0) };
        if new_ptr.is_null() {
            // SAFETY: We are just rebuilding the existing `Vec` with no changes.
            unsafe { rebuild(self, ptr, len, cap) };
            Err(AllocError)
        } else {
            // SAFETY: `ptr` has been reallocated with the layout for `new_cap` elements. New cap
            // is greater than `cap`, so it continues to be >= `len`.
            unsafe { rebuild(self, new_ptr.cast::<T>(), len, new_cap) };
            Ok(())
        }
    }
}

fn destructure<T>(v: &mut Vec<T>) -> (*mut T, usize, usize) {
    let mut tmp = Vec::new();
    core::mem::swap(&mut tmp, v);
    let mut tmp = ManuallyDrop::new(tmp);
    let len = tmp.len();
    let cap = tmp.capacity();
    (tmp.as_mut_ptr(), len, cap)
}

/// Rebuilds a `Vec` from a pointer, length, and capacity.
///
/// # Safety
///
/// The same as [`Vec::from_raw_parts`].
unsafe fn rebuild<T>(v: &mut Vec<T>, ptr: *mut T, len: usize, cap: usize) {
    // SAFETY: The safety requirements from this function satisfy those of `from_raw_parts`.
    let mut tmp = unsafe { Vec::from_raw_parts(ptr, len, cap) };
    core::mem::swap(&mut tmp, v);
}
