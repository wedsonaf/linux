// SPDX-License-Identifier: GPL-2.0

//! Kernel file systems.
//!
//! This module allows Rust code to register new kernel file systems.
//!
//! C headers: [`include/linux/fs.h`](../../include/linux/fs.h)

use crate::error::{code::*, from_result, to_result, Error, Result};
use crate::types::{ARef, AlwaysRefCounted, Either, Opaque};
use crate::{
    bindings, folio::LockedFolio, init::PinInit, str::CStr, time::Timespec, try_pin_init,
    ThisModule,
};
use core::{marker::PhantomData, marker::PhantomPinned, mem::ManuallyDrop, pin::Pin, ptr};
use macros::{pin_data, pinned_drop};

/// Maximum size of an inode.
pub const MAX_LFS_FILESIZE: i64 = bindings::MAX_LFS_FILESIZE;

/// A file system type.
pub trait FileSystem {
    /// The name of the file system type.
    const NAME: &'static CStr;

    /// Returns the parameters to initialise a super block.
    fn super_params(sb: &NewSuperBlock<Self>) -> Result<SuperParams>;

    /// Initialises and returns the root inode of the given superblock.
    ///
    /// This is called during initialisation of a superblock after [`FileSystem::super_params`] has
    /// completed successfully.
    fn init_root(sb: &SuperBlock<Self>) -> Result<ARef<INode<Self>>>;

    /// Reads directory entries from directory inodes.
    ///
    /// [`DirEmitter::pos`] holds the current position of the directory reader.
    fn read_dir(inode: &INode<Self>, emitter: &mut DirEmitter) -> Result;

    /// Returns the inode corresponding to the directory entry with the given name.
    fn lookup(parent: &INode<Self>, name: &[u8]) -> Result<ARef<INode<Self>>>;

    /// Reads the contents of the inode into the given folio.
    fn read_folio(inode: &INode<Self>, folio: LockedFolio<'_>) -> Result;
}

/// The types of directory entries reported by [`FileSystem::read_dir`].
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

impl From<INodeType> for DirEntryType {
    fn from(value: INodeType) -> Self {
        match value {
            INodeType::Dir => DirEntryType::Dir,
            INodeType::Reg => DirEntryType::Reg,
        }
    }
}

impl core::convert::TryFrom<u32> for DirEntryType {
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

/// A registration of a file system.
#[pin_data(PinnedDrop)]
pub struct Registration {
    #[pin]
    fs: Opaque<bindings::file_system_type>,
    #[pin]
    _pin: PhantomPinned,
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
            _pin: PhantomPinned,
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

/// The number of an inode.
pub type Ino = u64;

/// A node in the file system index (inode).
///
/// Wraps the kernel's `struct inode`.
///
/// # Invariants
///
/// Instances of this type are always ref-counted, that is, a call to `ihold` ensures that the
/// allocation remains valid at least until the matching call to `iput`.
#[repr(transparent)]
pub struct INode<T: FileSystem + ?Sized>(Opaque<bindings::inode>, PhantomData<T>);

impl<T: FileSystem + ?Sized> INode<T> {
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
        unsafe { &*(*self.0.get()).i_sb.cast() }
    }

    /// Returns the size of the inode contents.
    pub fn size(&self) -> i64 {
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
        unsafe { bindings::iput(obj.cast().as_ptr()) }
    }
}

/// An inode that is locked and hasn't been initialised yet.
#[repr(transparent)]
pub struct NewINode<T: FileSystem + ?Sized>(ARef<INode<T>>);

impl<T: FileSystem + ?Sized> NewINode<T> {
    /// Initialises the new inode with the given parameters.
    pub fn init(self, params: INodeParams) -> Result<ARef<INode<T>>> {
        // SAFETY: This is a new inode, so it's safe to manipulate it mutably.
        let inode = unsafe { &mut *self.0 .0.get() };

        let mode = match params.typ {
            INodeType::Dir => {
                inode.__bindgen_anon_3.i_fop = &Tables::<T>::DIR_FILE_OPERATIONS;
                inode.i_op = &Tables::<T>::DIR_INODE_OPERATIONS;
                bindings::S_IFDIR
            }
            INodeType::Reg => {
                // SAFETY: `generic_ro_fops` never changes, it's safe to reference it.
                inode.__bindgen_anon_3.i_fop = unsafe { &bindings::generic_ro_fops };
                inode.i_data.a_ops = &Tables::<T>::FILE_ADDRESS_SPACE_OPERATIONS;

                // SAFETY: The `i_mapping` pointer doesn't change and is valid.
                unsafe { bindings::mapping_set_large_folios(inode.i_mapping) };
                bindings::S_IFREG
            }
        };

        inode.i_mode = (params.mode & 0o777) | u16::try_from(mode)?;
        inode.i_size = params.size;
        inode.i_blocks = params.blocks;

        inode.__i_ctime = params.ctime.into();
        inode.i_mtime = params.mtime.into();
        inode.i_atime = params.atime.into();

        // SAFETY: inode is a new inode, so it is valid for write.
        unsafe {
            bindings::set_nlink(inode, params.nlink);
            bindings::i_uid_write(inode, params.uid);
            bindings::i_gid_write(inode, params.gid);
            bindings::unlock_new_inode(inode);
        }

        // SAFETY: We are manually destructuring `self` and preventing `drop` from being called.
        Ok(unsafe { (&ManuallyDrop::new(self).0 as *const ARef<INode<T>>).read() })
    }
}

impl<T: FileSystem + ?Sized> Drop for NewINode<T> {
    fn drop(&mut self) {
        // SAFETY: The new inode failed to be turned into an initialised inode, so it's safe (and
        // in fact required) to call `iget_failed` on it.
        unsafe { bindings::iget_failed(self.0 .0.get()) };
    }
}

/// The type of the inode.
#[derive(Copy, Clone)]
pub enum INodeType {
    /// Directory type.
    Dir,

    /// Regular file type.
    Reg,
}

/// Required inode parameters.
///
/// This is used when creating new inodes.
pub struct INodeParams {
    /// The access mode. It's a mask that grants execute (1), write (2) and read (4) access to
    /// everyone, the owner group, and the owner.
    pub mode: u16,

    /// Type of inode.
    ///
    /// Also carries additional per-type data.
    pub typ: INodeType,

    /// Size of the contents of the inode.
    ///
    /// Its maximum value is [`MAX_LFS_FILESIZE`].
    pub size: i64,

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

/// A file system super block.
///
/// Wraps the kernel's `struct super_block`.
#[repr(transparent)]
pub struct SuperBlock<T: FileSystem + ?Sized>(Opaque<bindings::super_block>, PhantomData<T>);

impl<T: FileSystem + ?Sized> SuperBlock<T> {
    /// Tries to get an existing inode or create a new one if it doesn't exist yet.
    pub fn get_or_create_inode(&self, ino: Ino) -> Result<Either<ARef<INode<T>>, NewINode<T>>> {
        // SAFETY: The only initialisation missing from the superblock is the root, and this
        // function is needed to create the root, so it's safe to call it.
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
            // `NewINode`.
            Ok(Either::Right(NewINode(unsafe {
                ARef::from_raw(inode.cast())
            })))
        }
    }
}

/// Required superblock parameters.
///
/// This is returned by implementations of [`FileSystem::super_params`].
pub struct SuperParams {
    /// The magic number of the superblock.
    pub magic: u32,

    /// The size of a block in powers of 2 (i.e., for a value of `n`, the size is `2^n`).
    pub blocksize_bits: u8,

    /// Maximum size of a file.
    ///
    /// The maximum allowed value is [`MAX_LFS_FILESIZE`].
    pub maxbytes: i64,

    /// Granularity of c/m/atime in ns (cannot be worse than a second).
    pub time_gran: u32,
}

/// A superblock that is still being initialised.
///
/// # Invariants
///
/// The superblock is a newly-created one and this is the only active pointer to it.
#[repr(transparent)]
pub struct NewSuperBlock<T: FileSystem + ?Sized>(bindings::super_block, PhantomData<T>);

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
            let sb = unsafe { &mut *sb_ptr.cast() };
            let params = T::super_params(sb)?;

            sb.0.s_magic = params.magic as _;
            sb.0.s_op = &Tables::<T>::SUPER_BLOCK;
            sb.0.s_maxbytes = params.maxbytes;
            sb.0.s_time_gran = params.time_gran;
            sb.0.s_blocksize_bits = params.blocksize_bits;
            sb.0.s_blocksize = 1;
            if sb.0.s_blocksize.leading_zeros() < params.blocksize_bits.into() {
                return Err(EINVAL);
            }
            sb.0.s_blocksize = 1 << sb.0.s_blocksize_bits;
            sb.0.s_flags |= bindings::SB_RDONLY;

            // SAFETY: The callback contract guarantees that `sb_ptr` is a unique pointer to a
            // newly-created (and initialised above) superblock.
            let sb = unsafe { &mut *sb_ptr.cast() };
            let root = T::init_root(sb)?;

            // Reject root inode if it belongs to a different superblock.
            if !ptr::eq(root.super_block(), sb) {
                return Err(EINVAL);
            }

            // SAFETY: `d_make_root` requires that `inode` be valid and referenced, which is the
            // case for this call.
            //
            // It takes over the inode, even on failure, so we don't need to clean it up.
            let dentry = unsafe { bindings::d_make_root(ManuallyDrop::new(root).0.get()) };
            if dentry.is_null() {
                return Err(ENOMEM);
            }

            // SAFETY: The callback contract guarantees that `sb_ptr` is a unique pointer to a
            // newly-created (and initialised above) superblock.
            unsafe { (*sb_ptr).s_root = dentry };

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

    const DIR_FILE_OPERATIONS: bindings::file_operations = bindings::file_operations {
        owner: ptr::null_mut(),
        llseek: Some(bindings::generic_file_llseek),
        read: Some(bindings::generic_read_dir),
        write: None,
        read_iter: None,
        write_iter: None,
        iopoll: None,
        iterate_shared: Some(Self::read_dir_callback),
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

    unsafe extern "C" fn read_dir_callback(
        file: *mut bindings::file,
        ctx_ptr: *mut bindings::dir_context,
    ) -> core::ffi::c_int {
        from_result(|| {
            // SAFETY: The C API guarantees that `file` is valid for read. And since `f_inode` is
            // immutable, we can read it directly.
            let inode = unsafe { &*(*file).f_inode.cast::<INode<T>>() };

            // SAFETY: The C API guarantees that this is the only reference to the `dir_context`
            // instance.
            let emitter = unsafe { &mut *ctx_ptr.cast::<DirEmitter>() };
            let orig_pos = emitter.pos();

            // Call the module implementation. We ignore errors if directory entries have been
            // succesfully emitted: this is because we want users to see them before the error.
            match T::read_dir(inode, emitter) {
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

    const DIR_INODE_OPERATIONS: bindings::inode_operations = bindings::inode_operations {
        lookup: Some(Self::lookup_callback),
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

    extern "C" fn lookup_callback(
        parent_ptr: *mut bindings::inode,
        dentry: *mut bindings::dentry,
        _flags: u32,
    ) -> *mut bindings::dentry {
        // SAFETY: The C API guarantees that `parent_ptr` is a valid inode.
        let parent = unsafe { &*parent_ptr.cast::<INode<T>>() };

        // SAFETY: The C API guarantees that `dentry` is valid for read. Since the name is
        // immutable, it's ok to read its length directly.
        let len = unsafe { (*dentry).d_name.__bindgen_anon_1.__bindgen_anon_1.len };
        let Ok(name_len) = usize::try_from(len) else {
            return ENOENT.to_ptr();
        };

        // SAFETY: The C API guarantees that `dentry` is valid for read. Since the name is
        // immutable, it's ok to read it directly.
        let name = unsafe { core::slice::from_raw_parts((*dentry).d_name.name, name_len) };
        match T::lookup(parent, name) {
            Err(e) => e.to_ptr(),
            // SAFETY: The returned inode is valid and referenced (by the type invariants), so
            // it is ok to transfer this increment to `d_splice_alias`.
            Ok(inode) => unsafe {
                bindings::d_splice_alias(ManuallyDrop::new(inode).0.get(), dentry)
            },
        }
    }

    const FILE_ADDRESS_SPACE_OPERATIONS: bindings::address_space_operations =
        bindings::address_space_operations {
            writepage: None,
            read_folio: Some(Self::read_folio_callback),
            writepages: None,
            dirty_folio: None,
            readahead: None,
            write_begin: None,
            write_end: None,
            bmap: None,
            invalidate_folio: None,
            release_folio: None,
            free_folio: None,
            direct_IO: None,
            migrate_folio: None,
            launder_folio: None,
            is_partially_uptodate: None,
            is_dirty_writeback: None,
            error_remove_page: None,
            swap_activate: None,
            swap_deactivate: None,
            swap_rw: None,
        };

    extern "C" fn read_folio_callback(
        _file: *mut bindings::file,
        folio: *mut bindings::folio,
    ) -> i32 {
        from_result(|| {
            // SAFETY: All pointers are valid and stable.
            let inode = unsafe {
                &*(*(*folio)
                    .__bindgen_anon_1
                    .page
                    .__bindgen_anon_1
                    .__bindgen_anon_1
                    .mapping)
                    .host
                    .cast::<INode<T>>()
            };

            // SAFETY: The C contract guarantees that the folio is valid and locked, with ownership
            // of the lock transferred to the callee (this function). The folio is also guaranteed
            // not to outlive this function.
            T::read_folio(inode, unsafe { LockedFolio::from_raw(folio) })?;
            Ok(0)
        })
    }
}

/// Directory entry emitter.
///
/// This is used in [`FileSystem::read_dir`] implementations to report the directory entry.
#[repr(transparent)]
pub struct DirEmitter(bindings::dir_context);

impl DirEmitter {
    /// Returns the current position of the emitter.
    pub fn pos(&self) -> i64 {
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
    pub fn emit(&mut self, pos_inc: i64, name: &[u8], ino: Ino, etype: DirEntryType) -> bool {
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
                name.as_ptr().cast(),
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
/// use kernel::fs::{DirEmitter, INode, NewSuperBlock, SuperBlock, SuperParams};
/// use kernel::prelude::*;
/// use kernel::{c_str, folio::LockedFolio, fs, types::ARef};
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
///     fn super_params(_: &NewSuperBlock<Self>) -> Result<SuperParams> {
///         todo!()
///     }
///     fn init_root(_sb: &SuperBlock<Self>) -> Result<ARef<INode<Self>>> {
///         todo!()
///     }
///     fn read_dir(_: &INode<Self>, _: &mut DirEmitter) -> Result {
///         todo!()
///     }
///     fn lookup(_: &INode<Self>, _: &[u8]) -> Result<ARef<INode<Self>>> {
///         todo!()
///     }
///     fn read_folio(_: &INode<Self>, _: LockedFolio<'_>) -> Result {
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
