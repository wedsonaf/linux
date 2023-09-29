// SPDX-License-Identifier: GPL-2.0

//! Kernel file systems.
//!
//! This module allows Rust code to register new kernel file systems.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use crate::error::{code::*, from_result, to_result, Error, Result};
use crate::types::Opaque;
use crate::{bindings, init::PinInit, str::CStr, try_pin_init, ThisModule};
use core::{marker::PhantomData, pin::Pin};
use macros::{pin_data, pinned_drop};
use sb::SuperBlock;

pub mod sb;

/// The offset of a file in a file system.
pub type Offset = i64;

/// Maximum size of an inode.
pub const MAX_LFS_FILESIZE: Offset = bindings::MAX_LFS_FILESIZE;

/// A file system type.
pub trait FileSystem {
    /// The name of the file system type.
    const NAME: &'static CStr;

    /// Returns the parameters to initialise a super block.
    fn super_params(sb: &SuperBlock<Self>) -> Result<sb::Params>;
}

/// A registration of a file system.
#[pin_data(PinnedDrop)]
pub struct Registration {
    #[pin]
    fs: Opaque<bindings::file_system_type>,
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
            fs <- Opaque::try_ffi_init(|fs_ptr: *mut bindings::file_system_type| {
                // SAFETY: `try_ffi_init` guarantees that `fs_ptr` is valid for write.
                unsafe { fs_ptr.write(bindings::file_system_type::default()) };

                // SAFETY: `try_ffi_init` guarantees that `fs_ptr` is valid for write, and it has
                // just been initialised above, so it's also valid for read.
                let fs = unsafe { &mut *fs_ptr };
                fs.owner = module.0;
                fs.name = T::NAME.as_char_ptr();
                fs.init_fs_context = Some(Self::init_fs_context_callback::<T>);
                fs.kill_sb = Some(Self::kill_sb_callback);
                fs.fs_flags = 0;

                // SAFETY: Pointers stored in `fs` are static so will live for as long as the
                // registration is active (it is undone in `drop`).
                to_result(unsafe { bindings::register_filesystem(fs_ptr) })
            }),
        })
    }

    unsafe extern "C" fn init_fs_context_callback<T: FileSystem + ?Sized>(
        fc_ptr: *mut bindings::fs_context,
    ) -> core::ffi::c_int {
        from_result(|| {
            // SAFETY: The C callback API guarantees that `fc_ptr` is valid.
            let fc = unsafe { &mut *fc_ptr };
            fc.ops = &Tables::<T>::CONTEXT;
            Ok(0)
        })
    }

    unsafe extern "C" fn kill_sb_callback(sb_ptr: *mut bindings::super_block) {
        // SAFETY: In `get_tree_callback` we always call `get_tree_nodev`, so `kill_anon_super` is
        // the appropriate function to call for cleanup.
        unsafe { bindings::kill_anon_super(sb_ptr) };
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

    unsafe extern "C" fn get_tree_callback(fc: *mut bindings::fs_context) -> core::ffi::c_int {
        // SAFETY: `fc` is valid per the callback contract. `fill_super_callback` also has
        // the right type and is a valid callback.
        unsafe { bindings::get_tree_nodev(fc, Some(Self::fill_super_callback)) }
    }

    unsafe extern "C" fn fill_super_callback(
        sb_ptr: *mut bindings::super_block,
        _fc: *mut bindings::fs_context,
    ) -> core::ffi::c_int {
        from_result(|| {
            // SAFETY: The callback contract guarantees that `sb_ptr` is a unique pointer to a
            // newly-created superblock.
            let new_sb = unsafe { SuperBlock::from_raw(sb_ptr) };

            // SAFETY: The callback contract guarantees that `sb_ptr`, from which `new_sb` is
            // derived, is valid for write.
            let sb = unsafe { &mut *new_sb.0.get() };
            sb.s_op = &Tables::<T>::SUPER_BLOCK;
            sb.s_flags |= bindings::SB_RDONLY;

            let params = T::super_params(new_sb)?;

            sb.s_magic = params.magic as core::ffi::c_ulong;
            sb.s_maxbytes = params.maxbytes;
            sb.s_time_gran = params.time_gran;
            sb.s_blocksize_bits = params.blocksize_bits;
            sb.s_blocksize = 1;
            if sb.s_blocksize.leading_zeros() < params.blocksize_bits.into() {
                return Err(EINVAL);
            }
            sb.s_blocksize = 1 << sb.s_blocksize_bits;

            // The following is scaffolding code that will be removed in a subsequent patch. It is
            // needed to build a root dentry, otherwise core code will BUG().
            // SAFETY: `sb` is the superblock being initialised, it is valid for read and write.
            let inode = unsafe { bindings::new_inode(sb) };
            if inode.is_null() {
                return Err(ENOMEM);
            }

            // SAFETY: `inode` is valid for write.
            unsafe { bindings::set_nlink(inode, 2) };

            {
                // SAFETY: This is a newly-created inode. No other references to it exist, so it is
                // safe to mutably dereference it.
                let inode = unsafe { &mut *inode };
                inode.i_ino = 1;
                inode.i_mode = (bindings::S_IFDIR | 0o755) as _;

                // SAFETY: `simple_dir_operations` never changes, it's safe to reference it.
                inode.__bindgen_anon_3.i_fop = unsafe { &bindings::simple_dir_operations };

                // SAFETY: `simple_dir_inode_operations` never changes, it's safe to reference it.
                inode.i_op = unsafe { &bindings::simple_dir_inode_operations };
            }

            // SAFETY: `d_make_root` requires that `inode` be valid and referenced, which is the
            // case for this call.
            //
            // It takes over the inode, even on failure, so we don't need to clean it up.
            let dentry = unsafe { bindings::d_make_root(inode) };
            if dentry.is_null() {
                return Err(ENOMEM);
            }

            sb.s_root = dentry;

            Ok(0)
        })
    }

    const SUPER_BLOCK: bindings::super_operations = bindings::super_operations {
        alloc_inode: None,
        destroy_inode: None,
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
        statfs: None,
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
/// use kernel::fs::sb::{self, SuperBlock};
/// use kernel::prelude::*;
/// use kernel::{c_str, fs};
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
///     const NAME: &'static CStr = c_str!("myfs");
///     fn super_params(_: &SuperBlock<Self>) -> Result<sb::Params> {
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
