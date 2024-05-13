// SPDX-License-Identifier: GPL-2.0

//! File system inodes.
//!
//! This module allows Rust code to implement inodes.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::{
    address_space, dentry, dentry::DEntry, file, sb::SuperBlock, FileSystem, Offset, UnspecifiedFS,
};
use crate::error::{code::*, Result};
use crate::types::{ARef, AlwaysRefCounted, Either, ForeignOwnable, Lockable, Locked, Opaque};
use crate::{bindings, block, str::CStr, str::CString, time::Timespec};
use core::mem::ManuallyDrop;
use core::{marker::PhantomData, ptr};
use macros::vtable;

/// The number of an inode.
pub type Ino = u64;

/// Operations implemented by inodes.
#[vtable]
pub trait Operations {
    /// File system that these operations are compatible with.
    type FileSystem: FileSystem + ?Sized;

    /// Returns the string that represents the name of the file a symbolic link inode points to.
    ///
    /// When `dentry` is `None`, `get_link` is called with the RCU read-side lock held, so it may
    /// not sleep. Implementations must return `Err(ECHILD)` for it to be called again without
    /// holding the RCU lock.
    fn get_link<'a>(
        _dentry: Option<&DEntry<Self::FileSystem>>,
        _inode: &'a INode<Self::FileSystem>,
    ) -> Result<Either<CString, &'a CStr>> {
        Err(ENOTSUPP)
    }

    /// Returns the inode corresponding to the directory entry with the given name.
    fn lookup(
        _parent: &Locked<&INode<Self::FileSystem>, ReadSem>,
        _dentry: dentry::Unhashed<'_, Self::FileSystem>,
    ) -> Result<Option<ARef<DEntry<Self::FileSystem>>>> {
        Err(ENOTSUPP)
    }
}

/// A node (inode) in the file index.
///
/// Wraps the kernel's `struct inode`.
///
/// # Invariants
///
/// Instances of this type are always ref-counted, that is, a call to `ihold` ensures that the
/// allocation remains valid at least until the matching call to `iput`.
#[repr(transparent)]
pub struct INode<T: FileSystem + ?Sized = UnspecifiedFS>(
    pub(crate) Opaque<bindings::inode>,
    PhantomData<T>,
);

impl<T: FileSystem + ?Sized> INode<T> {
    /// Creates a new inode reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    ///
    /// * `ptr` is valid and remains so for the lifetime of the returned object.
    /// * `ptr` has the correct file system type, or `T` is [`super::UnspecifiedFS`].
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

/// Indicates that the an inode's rw semapahore is locked in read (shared) mode.
pub struct ReadSem;

unsafe impl<T: FileSystem + ?Sized> Lockable<ReadSem> for INode<T> {
    fn raw_lock(&self) {
        // SAFETY: Since there's a reference to the inode, it must be valid.
        unsafe { bindings::inode_lock_shared(self.0.get()) };
    }

    unsafe fn unlock(&self) {
        // SAFETY: Since there's a reference to the inode, it must be valid. Additionally, the
        // safety requirements of this functino require that the inode be locked in read mode.
        unsafe { bindings::inode_unlock_shared(self.0.get()) };
    }
}

/// An inode that is locked and hasn't been initialised yet.
///
/// # Invariants
///
/// The inode is a new one, locked, and valid for write.
pub struct New<T: FileSystem + ?Sized>(
    pub(crate) ptr::NonNull<bindings::inode>,
    pub(crate) PhantomData<T>,
);

impl<T: FileSystem + ?Sized> New<T> {
    /// Initialises the new inode with the given parameters.
    pub fn init(mut self, params: Params) -> Result<ARef<INode<T>>> {
        // SAFETY: This is a new inode, so it's safe to manipulate it mutably.
        let inode = unsafe { self.0.as_mut() };
        let mode = match params.typ {
            Type::Dir => bindings::S_IFDIR,
            Type::Reg => {
                // SAFETY: The `i_mapping` pointer doesn't change and is valid.
                unsafe { bindings::mapping_set_large_folios(inode.i_mapping) };
                bindings::S_IFREG
            }
            Type::Lnk => {
                // If we are using `page_get_link`, we need to prevent the use of high mem.
                if !inode.i_op.is_null() {
                    // SAFETY: We just checked that `i_op` is non-null, and we always just set it
                    // to valid values.
                    if unsafe {
                        (*inode.i_op).get_link == bindings::page_symlink_inode_operations.get_link
                    } {
                        // SAFETY: `inode` is valid for write as it's a new inode.
                        unsafe { bindings::inode_nohighmem(inode) };
                    }
                }
                bindings::S_IFLNK
            }
            Type::Fifo => {
                // SAFETY: `inode` is valid for write as it's a new inode.
                unsafe { bindings::init_special_inode(inode, bindings::S_IFIFO as _, 0) };
                bindings::S_IFIFO
            }
            Type::Sock => {
                // SAFETY: `inode` is valid for write as it's a new inode.
                unsafe { bindings::init_special_inode(inode, bindings::S_IFSOCK as _, 0) };
                bindings::S_IFSOCK
            }
            Type::Chr(major, minor) => {
                // SAFETY: `inode` is valid for write as it's a new inode.
                unsafe {
                    bindings::init_special_inode(
                        inode,
                        bindings::S_IFCHR as _,
                        bindings::MKDEV(major, minor & bindings::MINORMASK),
                    )
                };
                bindings::S_IFCHR
            }
            Type::Blk(major, minor) => {
                // SAFETY: `inode` is valid for write as it's a new inode.
                unsafe {
                    bindings::init_special_inode(
                        inode,
                        bindings::S_IFBLK as _,
                        bindings::MKDEV(major, minor & bindings::MINORMASK),
                    )
                };
                bindings::S_IFBLK
            }
        };

        inode.i_mode = (params.mode & 0o777) | u16::try_from(mode)?;
        inode.i_size = params.size;
        inode.i_blocks = params.blocks;

        inode.__i_ctime = params.ctime.into();
        inode.__i_mtime = params.mtime.into();
        inode.__i_atime = params.atime.into();

        // SAFETY: inode is a new inode, so it is valid for write.
        unsafe {
            bindings::set_nlink(inode, params.nlink);
            bindings::i_uid_write(inode, params.uid);
            bindings::i_gid_write(inode, params.gid);
            bindings::unlock_new_inode(inode);
        }

        let manual = ManuallyDrop::new(self);
        // SAFETY: We transferred ownership of the refcount to `ARef` by preventing `drop` from
        // being called with the `ManuallyDrop` instance created above.
        Ok(unsafe { ARef::from_raw(manual.0.cast::<INode<T>>()) })
    }

    /// Sets the inode operations on this new inode.
    pub fn set_iops(&mut self, iops: Ops<T>) -> &mut Self {
        // SAFETY: By the type invariants, it's ok to modify the inode.
        let inode = unsafe { self.0.as_mut() };
        inode.i_op = iops.0;
        self
    }

    /// Sets the file operations on this new inode.
    pub fn set_fops(&mut self, fops: file::Ops<T>) -> &mut Self {
        // SAFETY: By the type invariants, it's ok to modify the inode.
        let inode = unsafe { self.0.as_mut() };
        inode.__bindgen_anon_3.i_fop = fops.0;
        self
    }

    /// Sets the address space operations on this new inode.
    pub fn set_aops(&mut self, aops: address_space::Ops<T>) -> &mut Self {
        // SAFETY: By the type invariants, it's ok to modify the inode.
        let inode = unsafe { self.0.as_mut() };
        inode.i_data.a_ops = aops.0;
        self
    }
}

impl<T: FileSystem + ?Sized> Drop for New<T> {
    fn drop(&mut self) {
        // SAFETY: The new inode failed to be turned into an initialised inode, so it's safe (and
        // in fact required) to call `iget_failed` on it.
        unsafe { bindings::iget_failed(self.0.as_ptr()) };
    }
}

/// The type of an inode.
#[derive(Copy, Clone)]
pub enum Type {
    /// Named pipe (first-in, first-out) type.
    Fifo,

    /// Character device type.
    Chr(u32, u32),

    /// Directory type.
    Dir,

    /// Block device type.
    Blk(u32, u32),

    /// Regular file type.
    Reg,

    /// Symbolic link type.
    Lnk,

    /// Named unix-domain socket type.
    Sock,
}

/// Required inode parameters.
///
/// This is used when creating new inodes.
pub struct Params {
    /// The access mode. It's a mask that grants execute (1), write (2) and read (4) access to
    /// everyone, the owner group, and the owner.
    pub mode: u16,

    /// Type of inode.
    ///
    /// Also carries additional per-type data.
    pub typ: Type,

    /// Size of the contents of the inode.
    ///
    /// Its maximum value is [`super::MAX_LFS_FILESIZE`].
    pub size: Offset,

    /// Number of blocks.
    pub blocks: block::Count,

    /// Number of links to the inode.
    pub nlink: u32,

    /// User id.
    pub uid: u32,

    /// Group id.
    pub gid: u32,

    /// Creation time.
    pub ctime: Timespec,

    /// Last modification time.
    pub mtime: Timespec,

    /// Last access time.
    pub atime: Timespec,
}

/// Represents inode operations.
pub struct Ops<T: FileSystem + ?Sized>(*const bindings::inode_operations, PhantomData<T>);

impl<T: FileSystem + ?Sized> Ops<T> {
    /// Returns inode operations for symbolic links that are stored in a single page.
    pub fn page_symlink_inode() -> Self {
        // SAFETY: This is a constant in C, it never changes.
        Self(
            unsafe { &bindings::page_symlink_inode_operations },
            PhantomData,
        )
    }

    /// Creates the inode operations from a type that implements the [`Operations`] trait.
    pub const fn new<U: Operations<FileSystem = T> + ?Sized>() -> Self {
        struct Table<T: Operations + ?Sized>(PhantomData<T>);
        impl<T: Operations + ?Sized> Table<T> {
            const TABLE: bindings::inode_operations = bindings::inode_operations {
                lookup: if T::HAS_LOOKUP {
                    Some(Self::lookup_callback)
                } else {
                    None
                },
                get_link: if T::HAS_GET_LINK {
                    Some(Self::get_link_callback)
                } else {
                    None
                },
                permission: None,
                get_inode_acl: None,
                readlink: None,
                create: None,
                link: None,
                unlink: None,
                symlink: None,
                mkdir: None,
                rmdir: None,
                mknod: None,
                rename: None,
                setattr: None,
                getattr: None,
                listxattr: None,
                fiemap: None,
                update_time: None,
                atomic_open: None,
                tmpfile: None,
                get_acl: None,
                set_acl: None,
                fileattr_set: None,
                fileattr_get: None,
                get_offset_ctx: None,
            };

            extern "C" fn lookup_callback(
                parent_ptr: *mut bindings::inode,
                dentry_ptr: *mut bindings::dentry,
                _flags: u32,
            ) -> *mut bindings::dentry {
                // SAFETY: The C API guarantees that `parent_ptr` is a valid inode.
                let parent = unsafe { INode::from_raw(parent_ptr) };

                // SAFETY: The C API guarantees that `dentry_ptr` is a valid dentry.
                let dentry = unsafe { DEntry::from_raw(dentry_ptr) };

                // SAFETY: The C API guarantees that the inode's rw semaphore is locked at least in
                // read mode. It does not expect callees to unlock it, so we make the locked object
                // manually dropped to avoid unlocking it.
                let locked = ManuallyDrop::new(unsafe { Locked::new(parent) });

                match T::lookup(&locked, dentry::Unhashed(dentry)) {
                    Err(e) => e.to_ptr(),
                    Ok(None) => ptr::null_mut(),
                    Ok(Some(ret)) => ManuallyDrop::new(ret).0.get(),
                }
            }

            extern "C" fn get_link_callback(
                dentry_ptr: *mut bindings::dentry,
                inode_ptr: *mut bindings::inode,
                delayed_call: *mut bindings::delayed_call,
            ) -> *const core::ffi::c_char {
                extern "C" fn drop_cstring(ptr: *mut core::ffi::c_void) {
                    // SAFETY: The argument came from a previous call to `into_foreign` below.
                    unsafe { CString::from_foreign(ptr) };
                }

                let dentry = if dentry_ptr.is_null() {
                    None
                } else {
                    // SAFETY: The C API guarantees that `dentry_ptr` is a valid dentry when it's
                    // non-null.
                    Some(unsafe { DEntry::from_raw(dentry_ptr) })
                };

                // SAFETY: The C API guarantees that `parent_ptr` is a valid inode.
                let inode = unsafe { INode::from_raw(inode_ptr) };

                match T::get_link(dentry, inode) {
                    Err(e) => e.to_ptr::<core::ffi::c_char>(),
                    Ok(Either::Right(str)) => str.as_char_ptr(),
                    Ok(Either::Left(str)) => {
                        let ptr = str.into_foreign();
                        unsafe {
                            bindings::set_delayed_call(
                                delayed_call,
                                Some(drop_cstring),
                                ptr.cast_mut(),
                            )
                        };

                        ptr.cast::<core::ffi::c_char>()
                    }
                }
            }
        }
        Self(&Table::<U>::TABLE, PhantomData)
    }
}
