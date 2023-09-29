// SPDX-License-Identifier: GPL-2.0

//! Kernel file systems.
//!
//! This module allows Rust code to register new kernel file systems.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use crate::error::{code::*, from_result, to_result, Error, Result};
use crate::types::{ForeignOwnable, Opaque};
use crate::{bindings, init::PinInit, mem_cache::MemCache, str::CStr, try_pin_init, ThisModule};
use core::{ffi, marker::PhantomData, mem::size_of, mem::ManuallyDrop, pin::Pin, ptr};
use dentry::DEntry;
use inode::INode;
use macros::{pin_data, pinned_drop};
use sb::SuperBlock;

pub mod address_space;
pub mod dentry;
pub mod file;
pub mod inode;
pub mod sb;

/// The offset of a file in a file system.
///
/// This is C's `loff_t`.
pub type Offset = i64;

/// An index into the page cache.
///
/// This is C's `pgoff_t`.
pub type PageOffset = usize;

/// Maximum size of an inode.
pub const MAX_LFS_FILESIZE: Offset = bindings::MAX_LFS_FILESIZE;

/// A file system type.
pub trait FileSystem {
    /// Data associated with each file system instance (super-block).
    type Data: ForeignOwnable + Send + Sync;

    /// Type of data associated with each inode.
    type INodeData: Send + Sync;

    /// The name of the file system type.
    const NAME: &'static CStr;

    /// Determines how superblocks for this file system type are keyed.
    const SUPER_TYPE: sb::Type = sb::Type::Independent;

    /// Determines if an implementation doesn't specify the required types.
    ///
    /// This is meant for internal use only.
    #[doc(hidden)]
    const IS_UNSPECIFIED: bool = false;

    /// Initialises the new superblock and returns the data to attach to it.
    fn fill_super(
        sb: &mut SuperBlock<Self, sb::New>,
        mapper: Option<inode::Mapper>,
    ) -> Result<Self::Data>;

    /// Initialises and returns the root inode of the given superblock.
    ///
    /// This is called during initialisation of a superblock after [`FileSystem::fill_super`] has
    /// completed successfully.
    fn init_root(sb: &SuperBlock<Self>) -> Result<dentry::Root<Self>>;

    /// Reads an xattr.
    ///
    /// Returns the number of bytes written to `outbuf`. If it is too small, returns the number of
    /// bytes needs to hold the attribute.
    fn read_xattr(
        _dentry: &DEntry<Self>,
        _inode: &INode<Self>,
        _name: &CStr,
        _outbuf: &mut [u8],
    ) -> Result<usize> {
        Err(EOPNOTSUPP)
    }

    /// Get filesystem statistics.
    fn statfs(_dentry: &DEntry<Self>) -> Result<Stat> {
        Err(ENOSYS)
    }
}

/// File system stats.
///
/// A subset of C's `kstatfs`.
pub struct Stat {
    /// Magic number of the file system.
    pub magic: usize,

    /// The maximum length of a file name.
    pub namelen: isize,

    /// Block size.
    pub bsize: isize,

    /// Number of files in the file system.
    pub files: u64,

    /// Number of blocks in the file system.
    pub blocks: u64,
}

/// A file system that is unspecified.
///
/// Attempting to get super-block or inode data from it will result in a build error.
pub struct UnspecifiedFS;

impl FileSystem for UnspecifiedFS {
    type Data = ();
    type INodeData = ();
    const NAME: &'static CStr = crate::c_str!("unspecified");
    const IS_UNSPECIFIED: bool = true;
    fn fill_super(_: &mut SuperBlock<Self, sb::New>, _: Option<inode::Mapper>) -> Result {
        Err(ENOTSUPP)
    }

    fn init_root(_: &SuperBlock<Self>) -> Result<dentry::Root<Self>> {
        Err(ENOTSUPP)
    }
}

/// A registration of a file system.
#[pin_data(PinnedDrop)]
pub struct Registration {
    #[pin]
    fs: Opaque<bindings::file_system_type>,
    inode_cache: Option<MemCache>,
}

// SAFETY: `Registration` doesn't provide any `&self` methods, so it is safe to pass references
// to it around.
unsafe impl Sync for Registration {}

// SAFETY: Both registration and unregistration are implemented in C and safe to be performed
// from any thread, so `Registration` is `Send`.
unsafe impl Send for Registration {}

impl Registration {
    /// Creates the initialiser of a new file system registration.
    pub fn new<T: FileSystem + ?Sized>(module: &'static ThisModule) -> impl PinInit<Self, Error> {
        try_pin_init!(Self {
            inode_cache: INode::<T>::new_cache()?,
            fs <- Opaque::try_ffi_init(|fs_ptr: *mut bindings::file_system_type| {
                // SAFETY: `try_ffi_init` guarantees that `fs_ptr` is valid for write.
                unsafe { fs_ptr.write(bindings::file_system_type::default()) };

                // SAFETY: `try_ffi_init` guarantees that `fs_ptr` is valid for write, and it has
                // just been initialised above, so it's also valid for read.
                let fs = unsafe { &mut *fs_ptr };
                fs.owner = module.0;
                fs.name = T::NAME.as_char_ptr();
                fs.init_fs_context = Some(Self::init_fs_context_callback::<T>);
                fs.kill_sb = Some(Self::kill_sb_callback::<T>);
                fs.fs_flags = if let sb::Type::BlockDev = T::SUPER_TYPE {
                    bindings::FS_REQUIRES_DEV as i32
                } else { 0 };

                // SAFETY: Pointers stored in `fs` are static so will live for as long as the
                // registration is active (it is undone in `drop`).
                to_result(unsafe { bindings::register_filesystem(fs_ptr) })
            }),
        })
    }

    unsafe extern "C" fn init_fs_context_callback<T: FileSystem + ?Sized>(
        fc_ptr: *mut bindings::fs_context,
    ) -> ffi::c_int {
        from_result(|| {
            // SAFETY: The C callback API guarantees that `fc_ptr` is valid.
            let fc = unsafe { &mut *fc_ptr };
            fc.ops = &Tables::<T>::CONTEXT;
            Ok(0)
        })
    }

    unsafe extern "C" fn kill_sb_callback<T: FileSystem + ?Sized>(
        sb_ptr: *mut bindings::super_block,
    ) {
        match T::SUPER_TYPE {
            // SAFETY: In `get_tree_callback` we always call `get_tree_bdev` for
            // `sb::Type::BlockDev`, so `kill_block_super` is the appropriate function to call
            // for cleanup.
            sb::Type::BlockDev => unsafe { bindings::kill_block_super(sb_ptr) },
            // SAFETY: In `get_tree_callback` we always call `get_tree_nodev` for
            // `sb::Type::Independent`, so `kill_anon_super` is the appropriate function to call
            // for cleanup.
            sb::Type::Independent => unsafe { bindings::kill_anon_super(sb_ptr) },
        }

        // SAFETY: The C API contract guarantees that `sb_ptr` is valid for read.
        let ptr = unsafe { (*sb_ptr).s_fs_info };
        if !ptr.is_null() {
            // SAFETY: The only place where `s_fs_info` is assigned is `NewSuperBlock::init`, where
            // it's initialised with the result of an `into_foreign` call. We checked above that
            // `ptr` is non-null because it would be null if we never reached the point where we
            // init the field.
            unsafe { T::Data::from_foreign(ptr) };
        }
    }
}

#[pinned_drop]
impl PinnedDrop for Registration {
    fn drop(self: Pin<&mut Self>) {
        // SAFETY: If an instance of `Self` has been successfully created, a call to
        // `register_filesystem` has necessarily succeeded. So it's ok to call
        // `unregister_filesystem` on the previously registered fs.
        unsafe { bindings::unregister_filesystem(self.fs.get()) };
    }
}

struct Tables<T: FileSystem + ?Sized>(T);
impl<T: FileSystem + ?Sized> Tables<T> {
    const CONTEXT: bindings::fs_context_operations = bindings::fs_context_operations {
        free: None,
        parse_param: None,
        get_tree: Some(Self::get_tree_callback),
        reconfigure: None,
        parse_monolithic: None,
        dup: None,
    };

    unsafe extern "C" fn get_tree_callback(fc: *mut bindings::fs_context) -> ffi::c_int {
        match T::SUPER_TYPE {
            // SAFETY: `fc` is valid per the callback contract. `fill_super_callback` also has
            // the right type and is a valid callback.
            sb::Type::BlockDev => unsafe {
                bindings::get_tree_bdev(fc, Some(Self::fill_super_callback))
            },
            // SAFETY: `fc` is valid per the callback contract. `fill_super_callback` also has
            // the right type and is a valid callback.
            sb::Type::Independent => unsafe {
                bindings::get_tree_nodev(fc, Some(Self::fill_super_callback))
            },
        }
    }

    unsafe extern "C" fn fill_super_callback(
        sb_ptr: *mut bindings::super_block,
        _fc: *mut bindings::fs_context,
    ) -> ffi::c_int {
        from_result(|| {
            // SAFETY: The callback contract guarantees that `sb_ptr` is a unique pointer to a
            // newly-created superblock.
            let new_sb = unsafe { SuperBlock::from_raw_mut(sb_ptr) };

            // SAFETY: The callback contract guarantees that `sb_ptr`, from which `new_sb` is
            // derived, is valid for write.
            let sb = unsafe { &mut *new_sb.0.get() };
            sb.s_op = &Tables::<T>::SUPER_BLOCK;
            sb.s_xattr = &Tables::<T>::XATTR_HANDLERS[0];
            sb.s_flags |= bindings::SB_RDONLY;

            let mapper = if matches!(T::SUPER_TYPE, sb::Type::BlockDev) {
                // SAFETY: This is the only mapper created for this inode, so it is unique.
                Some(unsafe { new_sb.bdev().inode().mapper() })
            } else {
                None
            };

            let data = T::fill_super(new_sb, mapper)?;

            // N.B.: Even on failure, `kill_sb` is called and frees the data.
            sb.s_fs_info = data.into_foreign().cast_mut();

            // SAFETY: The callback contract guarantees that `sb_ptr` is a unique pointer to a
            // newly-created (and initialised above) superblock. And we have just initialised
            // `s_fs_info`.
            let sb = unsafe { SuperBlock::from_raw(sb_ptr) };
            let root = T::init_root(sb)?;

            // Reject root inode if it belongs to a different superblock.
            if !ptr::eq(root.super_block(), sb) {
                return Err(EINVAL);
            }

            let dentry = ManuallyDrop::new(root).0.get();

            // SAFETY: The callback contract guarantees that `sb_ptr` is a unique pointer to a
            // newly-created (and initialised above) superblock.
            unsafe { (*sb_ptr).s_root = dentry };

            Ok(0)
        })
    }

    const SUPER_BLOCK: bindings::super_operations = bindings::super_operations {
        alloc_inode: if size_of::<T::INodeData>() != 0 {
            Some(INode::<T>::alloc_inode_callback)
        } else {
            None
        },
        destroy_inode: Some(INode::<T>::destroy_inode_callback),
        free_inode: None,
        dirty_inode: None,
        write_inode: None,
        drop_inode: None,
        evict_inode: None,
        put_super: None,
        sync_fs: None,
        freeze_super: None,
        freeze_fs: None,
        thaw_super: None,
        unfreeze_fs: None,
        statfs: Some(Self::statfs_callback),
        remount_fs: None,
        umount_begin: None,
        show_options: None,
        show_devname: None,
        show_path: None,
        show_stats: None,
        #[cfg(CONFIG_QUOTA)]
        quota_read: None,
        #[cfg(CONFIG_QUOTA)]
        quota_write: None,
        #[cfg(CONFIG_QUOTA)]
        get_dquots: None,
        nr_cached_objects: None,
        free_cached_objects: None,
        shutdown: None,
    };

    unsafe extern "C" fn statfs_callback(
        dentry_ptr: *mut bindings::dentry,
        buf: *mut bindings::kstatfs,
    ) -> ffi::c_int {
        from_result(|| {
            // SAFETY: The C API guarantees that `dentry_ptr` is a valid dentry.
            let dentry = unsafe { DEntry::from_raw(dentry_ptr) };
            let s = T::statfs(dentry)?;

            // SAFETY: The C API guarantees that `buf` is valid for read and write.
            let buf = unsafe { &mut *buf };
            buf.f_type = s.magic as ffi::c_long;
            buf.f_namelen = s.namelen as ffi::c_long;
            buf.f_bsize = s.bsize as ffi::c_long;
            buf.f_files = s.files;
            buf.f_blocks = s.blocks;
            Ok(0)
        })
    }

    const XATTR_HANDLERS: [*const bindings::xattr_handler; 2] = [&Self::XATTR_HANDLER, ptr::null()];

    const XATTR_HANDLER: bindings::xattr_handler = bindings::xattr_handler {
        name: ptr::null(),
        prefix: crate::c_str!("").as_char_ptr(),
        flags: 0,
        list: None,
        get: Some(Self::xattr_get_callback),
        set: None,
    };

    unsafe extern "C" fn xattr_get_callback(
        _handler: *const bindings::xattr_handler,
        dentry_ptr: *mut bindings::dentry,
        inode_ptr: *mut bindings::inode,
        name: *const ffi::c_char,
        buffer: *mut ffi::c_void,
        size: usize,
    ) -> ffi::c_int {
        from_result(|| {
            // SAFETY: The C API guarantees that `inode_ptr` is a valid dentry.
            let dentry = unsafe { DEntry::from_raw(dentry_ptr) };

            // SAFETY: The C API guarantees that `inode_ptr` is a valid inode.
            let inode = unsafe { INode::from_raw(inode_ptr) };

            // SAFETY: The c API guarantees that `name` is a valid null-terminated string. It
            // also guarantees that it's valid for the duration of the callback.
            let name = unsafe { CStr::from_char_ptr(name) };

            let (buf_ptr, size) = if buffer.is_null() {
                (ptr::NonNull::dangling().as_ptr(), 0)
            } else {
                (buffer.cast::<u8>(), size)
            };

            // SAFETY: The C API guarantees that `buffer` is at least `size` bytes in length.
            let buf = unsafe { core::slice::from_raw_parts_mut(buf_ptr, size) };
            let len = T::read_xattr(dentry, inode, name, buf)?;
            Ok(len.try_into()?)
        })
    }
}

/// Kernel module that exposes a single file system implemented by `T`.
#[pin_data]
pub struct Module<T: FileSystem + ?Sized> {
    #[pin]
    fs_reg: Registration,
    _p: PhantomData<T>,
}

impl<T: FileSystem + ?Sized + Sync + Send> crate::InPlaceModule for Module<T> {
    fn init(module: &'static ThisModule) -> impl PinInit<Self, Error> {
        try_pin_init!(Self {
            fs_reg <- Registration::new::<T>(module),
            _p: PhantomData,
        })
    }
}

/// Declares a kernel module that exposes a single file system.
///
/// The `type` argument must be a type which implements the [`FileSystem`] trait. Also accepts
/// various forms of kernel metadata.
///
/// # Examples
///
/// ```
/// # mod module_fs_sample {
/// use kernel::fs::{dentry, inode::INode, inode::Mapper, sb, sb::SuperBlock, self};
/// use kernel::prelude::*;
///
/// kernel::module_fs! {
///     type: MyFs,
///     name: "myfs",
///     author: "Rust for Linux Contributors",
///     description: "My Rust fs",
///     license: "GPL",
/// }
///
/// struct MyFs;
/// impl fs::FileSystem for MyFs {
///     type Data = ();
///     type INodeData = ();
///     const NAME: &'static CStr = kernel::c_str!("myfs");
///     fn fill_super(_: &mut SuperBlock<Self, sb::New>, _: Option<Mapper>) -> Result {
///         todo!()
///     }
///     fn init_root(_sb: &SuperBlock<Self>) -> Result<dentry::Root<Self>> {
///         todo!()
///     }
/// }
/// # }
/// ```
#[macro_export]
macro_rules! module_fs {
    (type: $type:ty, $($f:tt)*) => {
        type ModuleType = $crate::fs::Module<$type>;
        $crate::macros::module! {
            type: ModuleType,
            $($f)*
        }
    }
}
