// SPDX-License-Identifier: GPL-2.0

//! File system inodes.
//!
//! This module allows Rust code to implement inodes.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::{
    address_space, dentry, dentry::DEntry, file, mode, sb::SuperBlock, FileSystem, Offset,
};
use crate::error::{code::*, Result};
use crate::types::{ARef, AlwaysRefCounted, Either, ForeignOwnable, Opaque};
use crate::{bindings, container_of, mem_cache::MemCache, str::CStr, str::CString, time::Timespec};
use core::mem::{size_of, ManuallyDrop, MaybeUninit};
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

    /// Returns the data associated with the inode.
    pub fn data(&self) -> &T::INodeData {
        if T::IS_UNSPECIFIED {
            crate::build_error!("inode data type is unspecified");
        }
        let outerp = container_of!(self.0.get(), WithData<T::INodeData>, inode);
        // SAFETY: `self` is guaranteed to be valid by the existence of a shared reference
        // (`&self`) to it. Additionally, we know `T::INodeData` is always initialised in an
        // `INode`.
        unsafe { &*(*outerp).data.as_ptr() }
    }

    /// Returns the size of the inode contents.
    pub fn size(&self) -> Offset {
        // SAFETY: `self` is guaranteed to be valid by the existence of a shared reference.
        unsafe { bindings::i_size_read(self.0.get()) }
    }

    pub(crate) fn new_cache() -> Result<Option<MemCache>> {
        Ok(if size_of::<T::INodeData>() == 0 {
            None
        } else {
            Some(MemCache::try_new::<WithData<T::INodeData>>(
                T::NAME,
                Some(Self::inode_init_once_callback),
            )?)
        })
    }

    unsafe extern "C" fn inode_init_once_callback(outer_inode: *mut core::ffi::c_void) {
        let ptr = outer_inode.cast::<WithData<T::INodeData>>();

        // SAFETY: This is only used in `new`, so we know that we have a valid `inode::WithData`
        // instance whose inode part can be initialised.
        unsafe { bindings::inode_init_once(ptr::addr_of_mut!((*ptr).inode)) };
    }

    pub(crate) unsafe extern "C" fn alloc_inode_callback(
        sb: *mut bindings::super_block,
    ) -> *mut bindings::inode {
        // SAFETY: The callback contract guarantees that `sb` is valid for read.
        let super_type = unsafe { (*sb).s_type };

        // SAFETY: This callback is only used in `Registration`, so `super_type` is necessarily
        // embedded in a `Registration`, which is guaranteed to be valid because it has a
        // superblock associated to it.
        let reg = unsafe { &*container_of!(super_type, super::Registration, fs) };

        // SAFETY: `sb` and `cache` are guaranteed to be valid by the callback contract and by
        // the existence of a superblock respectively.
        let ptr = unsafe {
            bindings::alloc_inode_sb(sb, MemCache::ptr(&reg.inode_cache), bindings::GFP_KERNEL)
        }
        .cast::<WithData<T::INodeData>>();
        if ptr.is_null() {
            return ptr::null_mut();
        }
        ptr::addr_of_mut!((*ptr).inode)
    }

    pub(crate) unsafe extern "C" fn destroy_inode_callback(inode: *mut bindings::inode) {
        // SAFETY: By the C contract, `inode` is a valid pointer.
        let is_bad = unsafe { bindings::is_bad_inode(inode) };

        // SAFETY: The inode is guaranteed to be valid by the callback contract. Additionally, the
        // superblock is also guaranteed to still be valid by the inode existence.
        let super_type = unsafe { (*(*inode).i_sb).s_type };

        // SAFETY: This callback is only used in `Registration`, so `super_type` is necessarily
        // embedded in a `Registration`, which is guaranteed to be valid because it has a
        // superblock associated to it.
        let reg = unsafe { &*container_of!(super_type, super::Registration, fs) };
        let ptr = container_of!(inode, WithData<T::INodeData>, inode).cast_mut();

        if !is_bad {
            // SAFET: The API contract guarantees that `inode` is valid.
            if unsafe { (*inode).i_mode & mode::S_IFMT == mode::S_IFLNK } {
                // SAFETY: We just checked that the inode is a link.
                let lnk = unsafe { (*inode).__bindgen_anon_4.i_link };
                if !lnk.is_null() {
                    // SAFETY: This value is on link inode are only populated from with the result
                    // of `CString::into_foreign`.
                    unsafe { CString::from_foreign(lnk.cast::<core::ffi::c_void>()) };
                }
            }

            // SAFETY: The code either initialises the data or marks the inode as bad. Since the
            // inode is not bad, the data is initialised, and thus safe to drop.
            unsafe { ptr::drop_in_place((*ptr).data.as_mut_ptr()) };
        }

        if size_of::<T::INodeData>() == 0 {
            // SAFETY: When the size of `INodeData` is zero, we don't use a separate mem_cache, so
            // it is allocated from the regular mem_cache, which is what `free_inode_nonrcu` uses
            // to free the inode.
            unsafe { bindings::free_inode_nonrcu(inode) };
        } else {
            // The callback contract guarantees that the inode was previously allocated via the
            // `alloc_inode_callback` callback, so it is safe to free it back to the cache.
            unsafe {
                bindings::kmem_cache_free(
                    MemCache::ptr(&reg.inode_cache),
                    ptr.cast::<core::ffi::c_void>(),
                )
            };
        }
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

struct WithData<T> {
    data: MaybeUninit<T>,
    inode: bindings::inode,
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
    pub fn init(self, params: Params<T::INodeData>) -> Result<ARef<INode<T>>> {
        let outerp = container_of!(self.0.as_ptr(), WithData<T::INodeData>, inode);

        // SAFETY: This is a newly-created inode. No other references to it exist, so it is
        // safe to mutably dereference it.
        let outer = unsafe { &mut *outerp.cast_mut() };

        // N.B. We must always write this to a newly allocated inode because the free callback
        // expects the data to be initialised and drops it.
        outer.data.write(params.value);

        let inode = &mut outer.inode;
        let mode = match params.typ {
            Type::Dir => bindings::S_IFDIR,
            Type::Reg => {
                // SAFETY: The `i_mapping` pointer doesn't change and is valid.
                unsafe { bindings::mapping_set_large_folios(inode.i_mapping) };
                bindings::S_IFREG
            }
            Type::Lnk(str) => {
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
                if let Some(s) = str {
                    inode.__bindgen_anon_4.i_link = s.into_foreign().cast::<i8>().cast_mut();
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
    Lnk(Option<CString>),

    /// Named unix-domain socket type.
    Sock,
}

/// Required inode parameters.
///
/// This is used when creating new inodes.
pub struct Params<T> {
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

    /// Value to attach to this node.
    pub value: T,
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

    /// Returns inode operations for symbolic links that are stored in the `i_lnk` field.
    pub fn simple_symlink_inode() -> Self {
        // SAFETY: This is a constant in C, it never changes.
        Self(
            unsafe { &bindings::simple_symlink_inode_operations },
            PhantomData,
        )
    }

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
        }
        Self(&Table::<U>::TABLE, PhantomData)
    }
}
