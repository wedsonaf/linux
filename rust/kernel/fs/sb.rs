// SPDX-License-Identifier: GPL-2.0

//! File system super blocks.
//!
//! This module allows Rust code to use superblocks.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::inode::{self, INode, Ino};
use super::{FileSystem, Offset};
use crate::bindings;
use crate::error::{code::*, Result};
use crate::types::{ARef, Either, ForeignOwnable, Opaque};
use core::{marker::PhantomData, ptr};

/// A typestate for [`SuperBlock`] that indicates that it's a new one, so not fully initialized
/// yet.
pub struct New;

/// A typestate for [`SuperBlock`] that indicates that it's ready to be used.
pub struct Ready;

// SAFETY: Instances of `SuperBlock<T, Ready>` are only created after initialising the data.
unsafe impl DataInited for Ready {}

/// Indicates that a superblock in this typestate has data initialized.
///
/// # Safety
///
/// Implementers must ensure that `s_fs_info` is properly initialised in this state.
#[doc(hidden)]
pub unsafe trait DataInited {}

/// A file system super block.
///
/// Wraps the kernel's `struct super_block`.
#[repr(transparent)]
pub struct SuperBlock<T: FileSystem + ?Sized, S = Ready>(
    pub(crate) Opaque<bindings::super_block>,
    PhantomData<(S, T)>,
);

impl<T: FileSystem + ?Sized, S> SuperBlock<T, S> {
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

    /// Tries to get an existing inode or create a new one if it doesn't exist yet.
    pub fn get_or_create_inode(&self, ino: Ino) -> Result<Either<ARef<INode<T>>, inode::New<T>>> {
        // SAFETY: All superblock-related state needed by `iget_locked` is initialised by C code
        // before calling `fill_super_callback`, or by `fill_super_callback` itself before calling
        // `super_params`, which is the first function to see a new superblock.
        let inode =
            ptr::NonNull::new(unsafe { bindings::iget_locked(self.0.get(), ino) }).ok_or(ENOMEM)?;

        // SAFETY: `inode` is valid for read, but there could be concurrent writers (e.g., if it's
        // an already-initialised inode), so we use `read_volatile` to read its current state.
        let state = unsafe { ptr::read_volatile(ptr::addr_of!((*inode.as_ptr()).i_state)) };
        if state & u64::from(bindings::I_NEW) == 0 {
            // The inode is cached. Just return it.
            //
            // SAFETY: `inode` had its refcount incremented by `iget_locked`; this increment is now
            // owned by `ARef`.
            Ok(Either::Left(unsafe { ARef::from_raw(inode.cast()) }))
        } else {
            // SAFETY: The new inode is valid but not fully initialised yet, so it's ok to create a
            // `inode::New`.
            Ok(Either::Right(inode::New(inode, PhantomData)))
        }
    }
}

impl<T: FileSystem + ?Sized, S: DataInited> SuperBlock<T, S> {
    /// Returns the data associated with the superblock.
    pub fn data(&self) -> <T::Data as ForeignOwnable>::Borrowed<'_> {
        if T::IS_UNSPECIFIED {
            crate::build_error!("super block data type is unspecified");
        }

        // SAFETY: This method is only available if the typestate implements `DataInited`, whose
        // safety requirements include `s_fs_info` being properly initialised.
        let ptr = unsafe { (*self.0.get()).s_fs_info };
        unsafe { T::Data::borrow(ptr) }
    }
}

/// Required superblock parameters.
///
/// This is returned by implementations of [`FileSystem::super_params`].
pub struct Params<T: ForeignOwnable + Send + Sync> {
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

    /// Data to be associated with the superblock.
    pub data: T,
}
