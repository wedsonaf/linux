// SPDX-License-Identifier: GPL-2.0

//! File system super blocks.
//!
//! This module allows Rust code to use superblocks.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::{FileSystem, Offset};
use crate::{bindings, types::Opaque};
use core::marker::PhantomData;

/// A file system super block.
///
/// Wraps the kernel's `struct super_block`.
#[repr(transparent)]
pub struct SuperBlock<T: FileSystem + ?Sized>(
    pub(crate) Opaque<bindings::super_block>,
    PhantomData<T>,
);

impl<T: FileSystem + ?Sized> SuperBlock<T> {
    /// Creates a new superblock reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    ///
    /// * `ptr` is valid and remains so for the lifetime of the returned object.
    /// * `ptr` has the correct file system type, or `T` is [`super::UnspecifiedFS`].
    /// * `ptr` in the right typestate.
    pub(crate) unsafe fn from_raw<'a>(ptr: *mut bindings::super_block) -> &'a Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &*ptr.cast::<Self>() }
    }
}

/// Required superblock parameters.
///
/// This is returned by implementations of [`FileSystem::super_params`].
pub struct Params {
    /// The magic number of the superblock.
    pub magic: u32,

    /// The size of a block in powers of 2 (i.e., for a value of `n`, the size is `2^n`).
    pub blocksize_bits: u8,

    /// Maximum size of a file.
    ///
    /// The maximum allowed value is [`super::MAX_LFS_FILESIZE`].
    pub maxbytes: Offset,

    /// Granularity of c/m/atime in ns (cannot be worse than a second).
    pub time_gran: u32,
}
