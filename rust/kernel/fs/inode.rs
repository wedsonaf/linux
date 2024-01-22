// SPDX-License-Identifier: GPL-2.0

//! File system inodes.
//!
//! This module allows Rust code to implement inodes.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::{address_space, dentry, dentry::DEntry, file, sb::SuperBlock, FileSystem, Offset};
use crate::error::{code::*, Result};
use crate::types::{ARef, AlwaysRefCounted, Opaque};
use crate::{bindings, time::Timespec};
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

    /// Returns the inode corresponding to the directory entry with the given name.
    fn lookup(
        _parent: &INode<Self::FileSystem>,
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
    /// Directory type.
    Dir,

    /// Regular file type.
    Reg,
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
    pub blocks: u64,

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
    /// Creates the inode operations from a type that implements the [`Operations`] trait.
    pub const fn new<U: Operations<FileSystem = T> + ?Sized>() -> Self {
        struct Table<T: Operations + ?Sized>(PhantomData<T>);
        impl<T: Operations + ?Sized> Table<T> {
            extern "C" fn lookup_callback(
                parent_ptr: *mut bindings::inode,
                dentry_ptr: *mut bindings::dentry,
                _flags: u32,
            ) -> *mut bindings::dentry {
                // SAFETY: The C API guarantees that `parent_ptr` is a valid inode.
                let parent = unsafe { INode::from_raw(parent_ptr) };

                // SAFETY: The C API guarantees that `dentry_ptr` is a valid dentry.
                let dentry = unsafe { DEntry::from_raw(dentry_ptr) };

                match T::lookup(parent, dentry::Unhashed(dentry)) {
                    Err(e) => e.to_ptr(),
                    Ok(None) => ptr::null_mut(),
                    Ok(Some(ret)) => ManuallyDrop::new(ret).0.get(),
                }
            }

            const TABLE: bindings::inode_operations = bindings::inode_operations {
                lookup: if T::HAS_LOOKUP {
                    Some(Self::lookup_callback)
                } else {
                    None
                },
                get_link: None,
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
        }
        Self(&Table::<U>::TABLE, PhantomData)
    }
}
