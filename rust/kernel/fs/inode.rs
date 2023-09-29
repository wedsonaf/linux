// SPDX-License-Identifier: GPL-2.0

//! File system inodes.
//!
//! This module allows Rust code to implement inodes.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::{sb::SuperBlock, FileSystem, Offset};
use crate::bindings;
use crate::types::{AlwaysRefCounted, Opaque};
use core::{marker::PhantomData, ptr};

/// The number of an inode.
pub type Ino = u64;

/// A node (inode) in the file index.
///
/// Wraps the kernel's `struct inode`.
///
/// # Invariants
///
/// Instances of this type are always ref-counted, that is, a call to `ihold` ensures that the
/// allocation remains valid at least until the matching call to `iput`.
#[repr(transparent)]
pub struct INode<T: FileSystem + ?Sized>(pub(crate) Opaque<bindings::inode>, PhantomData<T>);

impl<T: FileSystem + ?Sized> INode<T> {
    /// Creates a new inode reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    ///
    /// * `ptr` is valid and remains so for the lifetime of the returned object.
    /// * `ptr` has the correct file system type, or `T` is [`super::UnspecifiedFS`].
    #[allow(dead_code)]
    pub(crate) unsafe fn from_raw<'a>(ptr: *mut bindings::inode) -> &'a Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &*ptr.cast::<Self>() }
    }

    /// Returns the number of the inode.
    pub fn ino(&self) -> Ino {
        // SAFETY: `i_ino` is immutable, and `self` is guaranteed to be valid by the existence of a
        // shared reference (&self) to it.
        unsafe { (*self.0.get()).i_ino }
    }

    /// Returns the super-block that owns the inode.
    pub fn super_block(&self) -> &SuperBlock<T> {
        // SAFETY: `i_sb` is immutable, and `self` is guaranteed to be valid by the existence of a
        // shared reference (&self) to it.
        unsafe { SuperBlock::from_raw((*self.0.get()).i_sb) }
    }

    /// Returns the size of the inode contents.
    pub fn size(&self) -> Offset {
        // SAFETY: `self` is guaranteed to be valid by the existence of a shared reference.
        unsafe { bindings::i_size_read(self.0.get()) }
    }
}

// SAFETY: The type invariants guarantee that `INode` is always ref-counted.
unsafe impl<T: FileSystem + ?Sized> AlwaysRefCounted for INode<T> {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::ihold(self.0.get()) };
    }

    unsafe fn dec_ref(obj: ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::iput(obj.as_ref().0.get()) }
    }
}
