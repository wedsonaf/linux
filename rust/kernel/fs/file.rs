// SPDX-License-Identifier: GPL-2.0

//! Files and file descriptors.
//!
//! This module allows Rust code to interact with and implement files.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h) and
//! [`include/linux/file.h`](srctree/include/linux/file.h)

use super::{dentry::DEntry, inode::INode, FileSystem, UnspecifiedFS};
use crate::{
    bindings,
    error::{code::*, Error, Result},
    types::{ARef, AlwaysRefCounted, Opaque},
};
use core::{marker::PhantomData, ptr};

/// Flags associated with a [`File`].
pub mod flags {
    /// File is opened in append mode.
    pub const O_APPEND: u32 = bindings::O_APPEND;

    /// Signal-driven I/O is enabled.
    pub const O_ASYNC: u32 = bindings::FASYNC;

    /// Close-on-exec flag is set.
    pub const O_CLOEXEC: u32 = bindings::O_CLOEXEC;

    /// File was created if it didn't already exist.
    pub const O_CREAT: u32 = bindings::O_CREAT;

    /// Direct I/O is enabled for this file.
    pub const O_DIRECT: u32 = bindings::O_DIRECT;

    /// File must be a directory.
    pub const O_DIRECTORY: u32 = bindings::O_DIRECTORY;

    /// Like [`O_SYNC`] except metadata is not synced.
    pub const O_DSYNC: u32 = bindings::O_DSYNC;

    /// Ensure that this file is created with the `open(2)` call.
    pub const O_EXCL: u32 = bindings::O_EXCL;

    /// Large file size enabled (`off64_t` over `off_t`).
    pub const O_LARGEFILE: u32 = bindings::O_LARGEFILE;

    /// Do not update the file last access time.
    pub const O_NOATIME: u32 = bindings::O_NOATIME;

    /// File should not be used as process's controlling terminal.
    pub const O_NOCTTY: u32 = bindings::O_NOCTTY;

    /// If basename of path is a symbolic link, fail open.
    pub const O_NOFOLLOW: u32 = bindings::O_NOFOLLOW;

    /// File is using nonblocking I/O.
    pub const O_NONBLOCK: u32 = bindings::O_NONBLOCK;

    /// Also known as `O_NDELAY`.
    ///
    /// This is effectively the same flag as [`O_NONBLOCK`] on all architectures
    /// except SPARC64.
    pub const O_NDELAY: u32 = bindings::O_NDELAY;

    /// Used to obtain a path file descriptor.
    pub const O_PATH: u32 = bindings::O_PATH;

    /// Write operations on this file will flush data and metadata.
    pub const O_SYNC: u32 = bindings::O_SYNC;

    /// This file is an unnamed temporary regular file.
    pub const O_TMPFILE: u32 = bindings::O_TMPFILE;

    /// File should be truncated to length 0.
    pub const O_TRUNC: u32 = bindings::O_TRUNC;

    /// Bitmask for access mode flags.
    ///
    /// # Examples
    ///
    /// ```
    /// use kernel::fs::file;
    /// # fn do_something() {}
    /// # let flags = 0;
    /// if (flags & file::flags::O_ACCMODE) == file::flags::O_RDONLY {
    ///     do_something();
    /// }
    /// ```
    pub const O_ACCMODE: u32 = bindings::O_ACCMODE;

    /// File is read only.
    pub const O_RDONLY: u32 = bindings::O_RDONLY;

    /// File is write only.
    pub const O_WRONLY: u32 = bindings::O_WRONLY;

    /// File can be both read and written.
    pub const O_RDWR: u32 = bindings::O_RDWR;
}

/// A file.
///
/// Wraps the kernel's `struct file`.
///
/// # Refcounting
///
/// Instances of this type are reference-counted. The reference count is incremented by the
/// `fget`/`get_file` functions and decremented by `fput`. The Rust type `ARef<File>` represents a
/// pointer that owns a reference count on the file.
///
/// Whenever a process opens a file descriptor (fd), it stores a pointer to the file in its `struct
/// files_struct`. This pointer owns a reference count to the file, ensuring the file isn't
/// prematurely deleted while the file descriptor is open. In Rust terminology, the pointers in
/// `struct files_struct` are `ARef<File>` pointers.
///
/// ## Light refcounts
///
/// Whenever a process has an fd to a file, it may use something called a "light refcount" as a
/// performance optimization. Light refcounts are acquired by calling `fdget` and released with
/// `fdput`. The idea behind light refcounts is that if the fd is not closed between the calls to
/// `fdget` and `fdput`, then the refcount cannot hit zero during that time, as the `struct
/// files_struct` holds a reference until the fd is closed. This means that it's safe to access the
/// file even if `fdget` does not increment the refcount.
///
/// The requirement that the fd is not closed during a light refcount applies globally across all
/// threads - not just on the thread using the light refcount. For this reason, light refcounts are
/// only used when the `struct files_struct` is not shared with other threads, since this ensures
/// that other unrelated threads cannot suddenly start using the fd and close it. Therefore,
/// calling `fdget` on a shared `struct files_struct` creates a normal refcount instead of a light
/// refcount.
///
/// Light reference counts must be released with `fdput` before the system call returns to
/// userspace. This means that if you wait until the current system call returns to userspace, then
/// all light refcounts that existed at the time have gone away.
///
/// ## Rust references
///
/// The reference type `&File` is similar to light refcounts:
///
/// * `&File` references don't own a reference count. They can only exist as long as the reference
///   count stays positive, and can only be created when there is some mechanism in place to ensure
///   this.
///
/// * The Rust borrow-checker normally ensures this by enforcing that the `ARef<File>` from which
///   a `&File` is created outlives the `&File`.
///
/// * Using the unsafe [`File::from_raw`] means that it is up to the caller to ensure that the
///   `&File` only exists while the reference count is positive.
///
/// * You can think of `fdget` as using an fd to look up an `ARef<File>` in the `struct
///   files_struct` and create an `&File` from it. The "fd cannot be closed" rule is like the Rust
///   rule "the `ARef<File>` must outlive the `&File`".
///
/// # Invariants
///
/// * Instances of this type are refcounted using the `f_count` field.
/// * If an fd with active light refcounts is closed, then it must be the case that the file
///   refcount is positive until there are no more light refcounts created from the fd that got
///   closed.
/// * A light refcount must be dropped before returning to userspace.
#[repr(transparent)]
pub struct File<T: FileSystem + ?Sized = UnspecifiedFS>(Opaque<bindings::file>, PhantomData<T>);

// SAFETY: By design, the only way to access a `File` is via an immutable reference or an `ARef`.
// This means that the only situation in which a `File` can be accessed mutably is when the
// refcount drops to zero and the destructor runs. It is safe for that to happen on any thread, so
// it is ok for this type to be `Send`.
unsafe impl<T: FileSystem + ?Sized> Send for File<T> {}

// SAFETY: All methods defined on `File` that take `&self` are safe to call even if other threads
// are concurrently accessing the same `struct file`, because those methods either access immutable
// properties or have proper synchronization to ensure that such accesses are safe.
unsafe impl<T: FileSystem + ?Sized> Sync for File<T> {}

impl<T: FileSystem + ?Sized> File<T> {
    /// Constructs a new `struct file` wrapper from a file descriptor.
    ///
    /// The file descriptor belongs to the current process.
    pub fn fget(fd: u32) -> Result<ARef<Self>, BadFdError> {
        // SAFETY: FFI call, there are no requirements on `fd`.
        let ptr = ptr::NonNull::new(unsafe { bindings::fget(fd) }).ok_or(BadFdError)?;

        // SAFETY: `bindings::fget` either returns null or a valid pointer to a file, and we
        // checked for null above.
        //
        // INVARIANT: `bindings::fget` creates a refcount, and we pass ownership of the refcount to
        // the new `ARef<File>`.
        Ok(unsafe { ARef::from_raw(ptr.cast()) })
    }

    /// Creates a reference to a [`File`] from a valid pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    ///
    /// * `ptr` is valid and remains so for the duration of 'a.
    /// * `ptr` has the correct file system type, or `T` is [`UnspecifiedFS`].
    pub unsafe fn from_raw<'a>(ptr: *const bindings::file) -> &'a Self {
        // SAFETY: The caller guarantees that the pointer is not dangling and stays valid for the
        // duration of 'a. The cast is okay because `File` is `repr(transparent)`.
        //
        // INVARIANT: The safety requirements guarantee that the refcount does not hit zero during
        // 'a.
        unsafe { &*ptr.cast::<Self>() }
    }

    /// Returns a raw pointer to the inner C struct.
    #[inline]
    pub fn as_ptr(&self) -> *mut bindings::file {
        self.0.get()
    }

    /// Returns the flags associated with the file.
    ///
    /// The flags are a combination of the constants in [`flags`].
    pub fn flags(&self) -> u32 {
        // This `read_volatile` is intended to correspond to a READ_ONCE call.
        //
        // SAFETY: The file is valid because the shared reference guarantees a nonzero refcount.
        //
        // TODO: Replace with `read_once` when available on the Rust side.
        unsafe { core::ptr::addr_of!((*self.as_ptr()).f_flags).read_volatile() }
    }

    /// Returns the inode associated with the file.
    pub fn inode(&self) -> &INode<T> {
        // SAFETY: `f_inode` is an immutable field, so it's safe to read it.
        unsafe { INode::from_raw((*self.0.get()).f_inode) }
    }

    /// Returns the dentry associated with the file.
    pub fn dentry(&self) -> &DEntry<T> {
        // SAFETY: `f_path` is an immutable field, so it's safe to read it. And will remain safe to
        // read while the `&self` is valid.
        unsafe { DEntry::from_raw((*self.0.get()).f_path.dentry) }
    }
}

// SAFETY: The type invariants guarantee that `File` is always ref-counted. This implementation
// makes `ARef<File>` own a normal refcount.
unsafe impl<T: FileSystem + ?Sized> AlwaysRefCounted for File<T> {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::get_file(self.as_ptr()) };
    }

    unsafe fn dec_ref(obj: ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::fput(obj.as_ref().0.get()) }
    }
}

/// Represents the `EBADF` error code.
///
/// Used for methods that can only fail with `EBADF`.
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct BadFdError;

impl From<BadFdError> for Error {
    fn from(_: BadFdError) -> Error {
        EBADF
    }
}

impl core::fmt::Debug for BadFdError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.pad("EBADF")
    }
}
