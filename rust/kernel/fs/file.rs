// SPDX-License-Identifier: GPL-2.0

//! Files and file descriptors.
//!
//! This module allows Rust code to interact with and implement files.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h) and
//! [`include/linux/file.h`](srctree/include/linux/file.h)

use super::{dentry::DEntry, inode, inode::INode, inode::Ino, FileSystem, Offset, UnspecifiedFS};
use crate::{
    bindings,
    error::{code::*, from_result, Error, Result},
    types::{ARef, AlwaysRefCounted, Opaque},
    user,
};
use core::{marker::PhantomData, ptr};
use macros::vtable;

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

/// Indicates how to interpret the `offset` argument in [`Operations::seek`].
#[repr(u32)]
pub enum Whence {
    /// `offset` bytes from the start of the file.
    Set = bindings::SEEK_SET,

    /// `offset` bytes from the end of the file.
    End = bindings::SEEK_END,

    /// `offset` bytes from the current location.
    Cur = bindings::SEEK_CUR,

    /// The next location greater than or equal to `offset` that contains data.
    Data = bindings::SEEK_DATA,

    /// The next location greater than or equal to `offset` that contains a hole.
    Hole = bindings::SEEK_HOLE,
}

impl TryFrom<i32> for Whence {
    type Error = crate::error::Error;

    fn try_from(v: i32) -> Result<Self> {
        match v {
            v if v == Self::Set as i32 => Ok(Self::Set),
            v if v == Self::End as i32 => Ok(Self::End),
            v if v == Self::Cur as i32 => Ok(Self::Cur),
            v if v == Self::Data as i32 => Ok(Self::Data),
            v if v == Self::Hole as i32 => Ok(Self::Hole),
            _ => Err(EDOM),
        }
    }
}

/// Generic implementation of [`Operations::seek`].
pub fn generic_seek(
    file: &File<impl FileSystem + ?Sized>,
    offset: Offset,
    whence: Whence,
) -> Result<Offset> {
    let n = unsafe { bindings::generic_file_llseek(file.0.get(), offset, whence as i32) };
    if n < 0 {
        Err(Error::from_errno(n.try_into()?))
    } else {
        Ok(n)
    }
}

/// Operations implemented by files.
#[vtable]
pub trait Operations {
    /// File system that these operations are compatible with.
    type FileSystem: FileSystem + ?Sized;

    /// Reads data from this file into the caller's buffer.
    fn read(
        _file: &File<Self::FileSystem>,
        _buffer: &mut user::Writer,
        _offset: &mut Offset,
    ) -> Result<usize> {
        Err(EINVAL)
    }

    /// Seeks the file to the given offset.
    fn seek(_file: &File<Self::FileSystem>, _offset: Offset, _whence: Whence) -> Result<Offset> {
        Err(EINVAL)
    }

    /// Reads directory entries from directory files.
    ///
    /// [`DirEmitter::pos`] holds the current position of the directory reader.
    fn read_dir(_file: &File<Self::FileSystem>, _emitter: &mut DirEmitter) -> Result {
        Err(EINVAL)
    }
}

/// Represents file operations.
pub struct Ops<T: FileSystem + ?Sized>(pub(crate) *const bindings::file_operations, PhantomData<T>);

impl<T: FileSystem + ?Sized> Ops<T> {
    /// Creates file operations from a type that implements the [`Operations`] trait.
    pub const fn new<U: Operations<FileSystem = T> + ?Sized>() -> Self {
        struct Table<T: Operations + ?Sized>(PhantomData<T>);
        impl<T: Operations + ?Sized> Table<T> {
            const TABLE: bindings::file_operations = bindings::file_operations {
                owner: ptr::null_mut(),
                llseek: if T::HAS_SEEK {
                    Some(Self::seek_callback)
                } else {
                    None
                },
                read: if T::HAS_READ {
                    Some(Self::read_callback)
                } else {
                    None
                },
                write: None,
                read_iter: None,
                write_iter: None,
                iopoll: None,
                iterate_shared: if T::HAS_READ_DIR {
                    Some(Self::read_dir_callback)
                } else {
                    None
                },
                poll: None,
                unlocked_ioctl: None,
                compat_ioctl: None,
                mmap: None,
                mmap_supported_flags: 0,
                open: None,
                flush: None,
                release: None,
                fsync: None,
                fasync: None,
                lock: None,
                get_unmapped_area: None,
                check_flags: None,
                flock: None,
                splice_write: None,
                splice_read: None,
                splice_eof: None,
                setlease: None,
                fallocate: None,
                show_fdinfo: None,
                copy_file_range: None,
                remap_file_range: None,
                fadvise: None,
                uring_cmd: None,
                uring_cmd_iopoll: None,
            };

            unsafe extern "C" fn seek_callback(
                file_ptr: *mut bindings::file,
                offset: bindings::loff_t,
                whence: i32,
            ) -> bindings::loff_t {
                from_result(|| {
                    // SAFETY: The C API guarantees that `file` is valid for the duration of the
                    // callback. Since this callback is specifically for filesystem T, we know `T`
                    // is the right filesystem.
                    let file = unsafe { File::from_raw(file_ptr) };
                    T::seek(file, offset, whence.try_into()?)
                })
            }

            unsafe extern "C" fn read_callback(
                file_ptr: *mut bindings::file,
                ptr: *mut core::ffi::c_char,
                len: usize,
                offset: *mut bindings::loff_t,
            ) -> isize {
                from_result(|| {
                    // SAFETY: The C API guarantees that `file` is valid for the duration of the
                    // callback. Since this callback is specifically for filesystem T, we know `T`
                    // is the right filesystem.
                    let file = unsafe { File::from_raw(file_ptr) };
                    let mut writer = user::Writer::new(ptr, len);

                    // SAFETY: The C API guarantees that `offset` is valid for read and write.
                    let read = T::read(file, &mut writer, unsafe { &mut *offset })?;
                    Ok(isize::try_from(read)?)
                })
            }

            unsafe extern "C" fn read_dir_callback(
                file_ptr: *mut bindings::file,
                ctx_ptr: *mut bindings::dir_context,
            ) -> core::ffi::c_int {
                from_result(|| {
                    // SAFETY: The C API guarantees that `file` is valid for the duration of the
                    // callback. Since this callback is specifically for filesystem T, we know `T`
                    // is the right filesystem.
                    let file = unsafe { File::from_raw(file_ptr) };

                    // SAFETY: The C API guarantees that this is the only reference to the
                    // `dir_context` instance.
                    let emitter = unsafe { &mut *ctx_ptr.cast::<DirEmitter>() };
                    let orig_pos = emitter.pos();

                    // Call the module implementation. We ignore errors if directory entries have
                    // been succesfully emitted: this is because we want users to see them before
                    // the error.
                    match T::read_dir(file, emitter) {
                        Ok(_) => Ok(0),
                        Err(e) => {
                            if emitter.pos() == orig_pos {
                                Err(e)
                            } else {
                                Ok(0)
                            }
                        }
                    }
                })
            }
        }
        Self(&Table::<U>::TABLE, PhantomData)
    }
}

/// The types of directory entries reported by [`Operations::read_dir`].
#[repr(u32)]
#[derive(Copy, Clone)]
pub enum DirEntryType {
    /// Unknown type.
    Unknown = bindings::DT_UNKNOWN,

    /// Named pipe (first-in, first-out) type.
    Fifo = bindings::DT_FIFO,

    /// Character device type.
    Chr = bindings::DT_CHR,

    /// Directory type.
    Dir = bindings::DT_DIR,

    /// Block device type.
    Blk = bindings::DT_BLK,

    /// Regular file type.
    Reg = bindings::DT_REG,

    /// Symbolic link type.
    Lnk = bindings::DT_LNK,

    /// Named unix-domain socket type.
    Sock = bindings::DT_SOCK,

    /// White-out type.
    Wht = bindings::DT_WHT,
}

impl From<inode::Type> for DirEntryType {
    fn from(value: inode::Type) -> Self {
        match value {
            inode::Type::Dir => DirEntryType::Dir,
        }
    }
}

impl TryFrom<u32> for DirEntryType {
    type Error = crate::error::Error;

    fn try_from(v: u32) -> Result<Self> {
        match v {
            v if v == Self::Unknown as u32 => Ok(Self::Unknown),
            v if v == Self::Fifo as u32 => Ok(Self::Fifo),
            v if v == Self::Chr as u32 => Ok(Self::Chr),
            v if v == Self::Dir as u32 => Ok(Self::Dir),
            v if v == Self::Blk as u32 => Ok(Self::Blk),
            v if v == Self::Reg as u32 => Ok(Self::Reg),
            v if v == Self::Lnk as u32 => Ok(Self::Lnk),
            v if v == Self::Sock as u32 => Ok(Self::Sock),
            v if v == Self::Wht as u32 => Ok(Self::Wht),
            _ => Err(EDOM),
        }
    }
}

/// Directory entry emitter.
///
/// This is used in [`Operations::read_dir`] implementations to report the directory entry.
#[repr(transparent)]
pub struct DirEmitter(bindings::dir_context);

impl DirEmitter {
    /// Returns the current position of the emitter.
    pub fn pos(&self) -> Offset {
        self.0.pos
    }

    /// Emits a directory entry.
    ///
    /// `pos_inc` is the number with which to increment the current position on success.
    ///
    /// `name` is the name of the entry.
    ///
    /// `ino` is the inode number of the entry.
    ///
    /// `etype` is the type of the entry.
    ///
    /// Returns `false` when the entry could not be emitted, possibly because the user-provided
    /// buffer is full.
    pub fn emit(&mut self, pos_inc: Offset, name: &[u8], ino: Ino, etype: DirEntryType) -> bool {
        let Ok(name_len) = i32::try_from(name.len()) else {
            return false;
        };

        let Some(actor) = self.0.actor else {
            return false;
        };

        let Some(new_pos) = self.0.pos.checked_add(pos_inc) else {
            return false;
        };

        // SAFETY: `name` is valid at least for the duration of the `actor` call.
        let ret = unsafe {
            actor(
                &mut self.0,
                name.as_ptr().cast::<i8>(),
                name_len,
                self.0.pos,
                ino,
                etype as _,
            )
        };
        if ret {
            self.0.pos = new_pos;
        }
        ret
    }
}
