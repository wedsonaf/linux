// SPDX-License-Identifier: GPL-2.0

//! Extensions to [`Box`] for fallible allocations.

use super::Flags;
use alloc::boxed::Box;
use core::alloc::AllocError;
use core::mem::MaybeUninit;
use core::result::Result;

/// Extensions to [`Box`].
pub trait BoxExt<T>: Sized {
    /// Allocates a new box.
    ///
    /// The allocation may fail, in which case an error is returned.
    fn new(x: T, flags: Flags) -> Result<Self, AllocError>;

    /// Allocates a new uninitialised box.
    ///
    /// The allocation may fail, in which case an error is returned.
    fn new_uninit(flags: Flags) -> Result<Box<MaybeUninit<T>>, AllocError>;
}

impl<T> BoxExt<T> for Box<T> {
    #[cfg(any(test, testlib))]
    fn new(x: T, _flags: Flags) -> Result<Self, AllocError> {
        Ok(Box::new(x))
    }

    #[cfg(not(any(test, testlib)))]
    fn new(x: T, flags: Flags) -> Result<Self, AllocError> {
        let ptr = if core::mem::size_of::<T>() == 0 {
            core::ptr::NonNull::<T>::dangling().as_ptr()
        } else {
            let layout = core::alloc::Layout::new::<T>();

            // SAFETY: Memory is being allocated (first arg is null). The only other source of
            // safety issues is sleeping on atomic context, which is addressed by klint.
            let ptr = unsafe {
                super::allocator::krealloc_aligned(core::ptr::null_mut(), layout, flags.0)
            };
            if ptr.is_null() {
                return Err(AllocError);
            }

            let ptr = ptr.cast::<T>();

            // SAFETY: We just allocated the memory above, it is valid for write.
            unsafe { ptr.write(x) };
            ptr
        };

        // SAFETY: For non-zero-sized types, we allocate above using the global allocator. For
        // zero-sized types, we use `NonNull::dangling`.
        Ok(unsafe { Box::from_raw(ptr) })
    }

    fn new_uninit(flags: Flags) -> Result<Box<MaybeUninit<T>>, AllocError> {
        <Box<_> as BoxExt<_>>::new(MaybeUninit::<T>::uninit(), flags)
    }
}
