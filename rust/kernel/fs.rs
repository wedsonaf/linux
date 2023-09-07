// SPDX-License-Identifier: GPL-2.0

//! A kernel file system.
//!
//! This module allows Rust code to register new kernel file systems.
//!
//! C headers: [`include/linux/fs.h`](../../include/linux/fs.h)

pub mod buffer;

pub use bindings::MAX_LFS_FILESIZE;
pub use bindings::{S_IFBLK, S_IFCHR, S_IFDIR, S_IFIFO, S_IFLNK, S_IFMT, S_IFREG, S_IFSOCK};

/// Read-only file systems.
pub mod ro {
    use crate::error::{code::*, from_result, to_result, Error, Result};
    use crate::types::{ARef, AlwaysRefCounted, Either, ForeignOwnable, Opaque, ScopeGuard};
    use crate::{
        bindings, container_of, folio::LockedFolio, init::PinInit, str::CStr, try_pin_init,
        ThisModule,
    };
    use core::mem::{align_of, size_of, ManuallyDrop, MaybeUninit};
    use core::{marker::PhantomData, marker::PhantomPinned, pin::Pin, ptr};
    use macros::{pin_data, pinned_drop};

    /// Type of superblock keying.
    ///
    /// It determines how C's `fs_context_operations::get_tree` is implemented.
    pub enum Super {
        /// Multiple independent superblocks may exist.
        Independent,

        /// Uses a block device.
        BlockDev,
    }

    /// A read-only file system type.
    pub trait Type {
        /// Data associated with each file system instance (super-block).
        type Data: ForeignOwnable + Send + Sync;

        /// Type of data allocated for each inode.
        type INodeData: Send + Sync;

        /// The name of the file system type.
        const NAME: &'static CStr;

        /// Determines how superblocks for this file system type are keyed.
        const SUPER_TYPE: Super = Super::Independent;

        /// Initialises a super block for this file system type.
        fn fill_super(sb: NewSuperBlock<'_, Self>) -> Result<&SuperBlock<Self>>;

        /// Reads directory entries.
        ///
        /// `pos` is the current position of the directory reader.
        fn read_dir(
            inode: &INode<Self>,
            pos: i64,
            report: impl FnMut(&[u8], i64, u64, DirEntryType) -> bool,
        ) -> Result<i64>;

        /// Looks up an entry with the given under the given parent inode.
        fn lookup(parent: &INode<Self>, name: &[u8]) -> Result<ARef<INode<Self>>>;

        /// Reads the contents of the inode into the given folio.
        fn read_folio(inode: &INode<Self>, folio: crate::folio::LockedFolio<'_>) -> Result;
    }

    /// The types of directory entries reported by [`Type::read_dir`].
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

    struct MemCache {
        ptr: *mut bindings::kmem_cache,
    }

    impl MemCache {
        fn try_new<T>(
            name: &'static CStr,
            init: Option<unsafe extern "C" fn(*mut core::ffi::c_void)>,
        ) -> Result<Self> {
            // SAFETY: `name` is static, so always valid.
            let ptr = unsafe {
                bindings::kmem_cache_create(
                    name.as_char_ptr(),
                    size_of::<T>().try_into()?,
                    align_of::<T>().try_into()?,
                    bindings::SLAB_RECLAIM_ACCOUNT
                        | bindings::SLAB_MEM_SPREAD
                        | bindings::SLAB_ACCOUNT,
                    init,
                )
            };
            if ptr.is_null() {
                return Err(ENOMEM);
            }

            Ok(Self { ptr })
        }

        fn ptr(c: &Option<Self>) -> *mut bindings::kmem_cache {
            match c {
                Some(m) => m.ptr,
                None => ptr::null_mut(),
            }
        }
    }

    impl Drop for MemCache {
        fn drop(&mut self) {
            // SAFETY: Just an FFI call with no additional safety requirements.
            unsafe { bindings::rcu_barrier() };
            unsafe { bindings::kmem_cache_destroy(self.ptr) };
        }
    }

    /// A registration of a read-only file system.
    #[pin_data(PinnedDrop)]
    pub struct Registration {
        #[pin]
        fs: Opaque<bindings::file_system_type>,
        inode_cache: Option<MemCache>,
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
        /// Creates a new file system registration.
        #[allow(clippy::new_ret_no_self)]
        pub fn new<T: Type + ?Sized>(module: &'static ThisModule) -> impl PinInit<Self, Error> {
            try_pin_init!(Self {
                _pin: PhantomPinned,
                inode_cache: {
                    if size_of::<T::INodeData>() == 0 {
                        None
                    } else {
                        Some(MemCache::try_new::<INodeWithData<T::INodeData>>(T::NAME, Some(Self::inode_init_once_callback::<T>))?)
                    }
                },
                fs <- Opaque::try_ffi_init(|fs_ptr| {
                    // SAFETY: `pin_init_from_closure` guarantees that `fs_ptr` is valid for write.
                    let fs = unsafe { &mut *fs_ptr };
                    *fs = bindings::file_system_type::default();
                    fs.owner = module.0;
                    fs.name = T::NAME.as_char_ptr();
                    fs.init_fs_context = Some(Self::init_fs_context_callback::<T>);
                    fs.kill_sb = Some(Self::kill_sb_callback::<T>);
                    fs.fs_flags = if let Super::BlockDev = T::SUPER_TYPE {
                        bindings::FS_REQUIRES_DEV as i32
                    } else { 0 };

                    // SAFETY: Pointers stored in `fs` are static so will live for as long as the
                    // registration is active (it is undone in `drop`).
                    to_result(unsafe { bindings::register_filesystem(fs_ptr) })
                }),
            })
        }

        unsafe extern "C" fn init_fs_context_callback<T: Type + ?Sized>(
            fc_ptr: *mut bindings::fs_context,
        ) -> core::ffi::c_int {
            from_result(|| {
                // SAFETY: The C callback API guarantees that `fc_ptr` is valid.
                let fc = unsafe { &mut *fc_ptr };
                fc.ops = &Tables::<T>::CONTEXT;
                Ok(0)
            })
        }

        unsafe extern "C" fn kill_sb_callback<T: Type + ?Sized>(
            sb_ptr: *mut bindings::super_block,
        ) {
            match T::SUPER_TYPE {
                Super::BlockDev => unsafe { bindings::kill_block_super(sb_ptr) },
                Super::Independent => unsafe { bindings::kill_anon_super(sb_ptr) },
            }

            let ptr = unsafe { (*sb_ptr).s_fs_info };
            if !ptr.is_null() {
                // SAFETY: The only place where `s_fs_info` is assigned is `NewSuperBlock::init`,
                // where it's initialised with the result of a `into_foreign` call. We checked
                // above that `ptr` is non-null because it would be null if we never reached the
                // point where we init the field.
                unsafe { T::Data::from_foreign(ptr) };
            }
        }

        unsafe extern "C" fn inode_init_once_callback<T: Type + ?Sized>(
            outer_inode: *mut core::ffi::c_void,
        ) {
            let ptr = outer_inode.cast::<INodeWithData<T::INodeData>>();
            // This is only used in `new`, so we know that we have a valid `INodeWithData`
            // instance whose inode part can be initialised.
            unsafe { bindings::inode_init_once(ptr::addr_of_mut!((*ptr).inode)) };
        }
    }

    #[pinned_drop]
    impl PinnedDrop for Registration {
        fn drop(self: Pin<&mut Self>) {
            unsafe { bindings::unregister_filesystem(self.fs.get()) };
        }
    }

    /// Wraps the kernel's `struct inode`.
    ///
    /// # Invariants
    ///
    /// Instances of this type are always ref-counted, that is, a call to `ihold` ensures that the
    /// allocation remains valid at least until the matching call to `iput`.
    #[repr(transparent)]
    pub struct INode<T: Type + ?Sized>(Opaque<bindings::inode>, PhantomData<T>);

    impl<T: Type + ?Sized> INode<T> {
        /// Returns the number of the inode.
        pub fn ino(&self) -> u64 {
            // SAFETY: `i_ino` is immutable, and `self` is guaranteed to be valid by the existence
            // of a shared reference (&self) to it.
            unsafe { (*self.0.get()).i_ino }
        }

        /// Returns the super-block that owns the inode.
        pub fn super_block(&self) -> &SuperBlock<T> {
            unsafe { &*(*self.0.get()).i_sb.cast() }
        }

        /// Returns the data associated with the inode.
        pub fn data(&self) -> &T::INodeData {
            let outerp = container_of!(self.0.get(), INodeWithData<T::INodeData>, inode);
            unsafe { &*(*outerp).data.as_ptr() }
        }

        /// Returns the size of the inode contents.
        pub fn size(&self) -> i64 {
            unsafe { bindings::i_size_read(self.0.get()) }
        }
    }

    // SAFETY: The type invariants guarantee that `INode` is always ref-counted.
    unsafe impl<T: Type + ?Sized> AlwaysRefCounted for INode<T> {
        fn inc_ref(&self) {
            // SAFETY: The existence of a shared reference means that the refcount is nonzero.
            unsafe { bindings::ihold(self.0.get()) };
        }

        unsafe fn dec_ref(obj: ptr::NonNull<Self>) {
            // SAFETY: The safety requirements guarantee that the refcount is nonzero.
            unsafe { bindings::iput(obj.cast().as_ptr()) }
        }
    }

    struct INodeWithData<T> {
        data: MaybeUninit<T>,
        inode: bindings::inode,
    }

    /// An inode that is locked and hasn't been initialised yet.
    #[repr(transparent)]
    pub struct NewINode<T: Type + ?Sized>(ARef<INode<T>>);

    impl<T: Type + ?Sized> NewINode<T> {
        /// Initialises the new inode with the given parameters.
        pub fn init(self, params: INodeParams<T::INodeData>) -> Result<ARef<INode<T>>> {
            let outerp = container_of!(self.0 .0.get(), INodeWithData<T::INodeData>, inode);

            // SAFETY: This is a newly-created inode. No other references to it exist, so it is
            // safe to mutably dereference it.
            let outer = unsafe { &mut *(outerp.cast_mut()) };

            // N.B. We must always write this to a newly allocated inode because the free callback
            // expects the data to be initialised and drops it.
            outer.data.write(params.value);

            let inode = &mut outer.inode;

            let mode = match params.typ {
                INodeType::Dir => {
                    inode.__bindgen_anon_3.i_fop = &Tables::<T>::DIR_FILE_OPERATIONS;
                    inode.i_op = &Tables::<T>::DIR_INODE_OPERATIONS;
                    bindings::S_IFDIR
                }
                INodeType::Reg => {
                    inode.__bindgen_anon_3.i_fop = unsafe { &bindings::generic_ro_fops };
                    inode.i_data.a_ops = &Tables::<T>::FILE_ADDRESS_SPACE_OPERATIONS;
                    unsafe { bindings::mapping_set_large_folios(inode.i_mapping) };
                    bindings::S_IFREG
                }
                INodeType::Lnk => {
                    inode.i_op = &Tables::<T>::LNK_INODE_OPERATIONS;
                    inode.i_data.a_ops = &Tables::<T>::FILE_ADDRESS_SPACE_OPERATIONS;
                    unsafe { bindings::inode_nohighmem(inode) };
                    bindings::S_IFLNK
                }
                INodeType::Fifo => {
                    unsafe { bindings::init_special_inode(inode, bindings::S_IFIFO as _, 0) };
                    bindings::S_IFIFO
                }
                INodeType::Sock => {
                    unsafe { bindings::init_special_inode(inode, bindings::S_IFSOCK as _, 0) };
                    bindings::S_IFSOCK
                }
                INodeType::Chr(major, minor) => {
                    unsafe {
                        bindings::init_special_inode(
                            inode,
                            bindings::S_IFCHR as _,
                            bindings::MKDEV(major, minor & bindings::MINORMASK),
                        )
                    };
                    bindings::S_IFCHR
                }
                INodeType::Blk(major, minor) => {
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

            // SAFETY: `current_time` requires that `inode.sb` be valid, which is the case here
            // since we allocated the inode through the superblock.
            inode.i_ctime.tv_sec = params.ctime.secs.try_into()?;
            inode.i_ctime.tv_nsec = params.ctime.nsecs.try_into()?;
            inode.i_mtime.tv_sec = params.mtime.secs.try_into()?;
            inode.i_mtime.tv_nsec = params.mtime.nsecs.try_into()?;
            inode.i_atime.tv_sec = params.atime.secs.try_into()?;
            inode.i_atime.tv_nsec = params.atime.nsecs.try_into()?;
            inode.i_mode = (params.mode & 0o777) | u16::try_from(mode)?;
            inode.i_size = params.size;
            inode.i_blocks = params.blocks;

            unsafe { bindings::set_nlink(inode, params.nlink) };
            unsafe { bindings::i_uid_write(inode, params.uid) };
            unsafe { bindings::i_gid_write(inode, params.gid) };

            unsafe { bindings::unlock_new_inode(inode) };
            Ok(unsafe { ((&ManuallyDrop::new(self).0) as *const ARef<INode<T>>).read() })
        }
    }

    impl<T: Type + ?Sized> Drop for NewINode<T> {
        fn drop(&mut self) {
            unsafe { bindings::iget_failed(self.0 .0.get()) };
        }
    }

    /// A file system super block.
    ///
    /// Wraps the kernel's `struct super_block`.
    #[repr(transparent)]
    pub struct SuperBlock<T: Type + ?Sized>(Opaque<bindings::super_block>, PhantomData<T>);

    impl<T: Type + ?Sized> SuperBlock<T> {
        /// Returns the data associated with the superblock.
        pub fn data(&self) -> <T::Data as ForeignOwnable>::Borrowed<'_> {
            let ptr = unsafe { (*self.0.get()).s_fs_info };
            unsafe { T::Data::borrow(ptr) }
        }

        /// Tries to get an existing inode or create a new one if it doesn't exist yet.
        pub fn get_or_create_inode(&self, ino: u64) -> Result<Either<ARef<INode<T>>, NewINode<T>>> {
            let inode = ptr::NonNull::new(unsafe { bindings::iget_locked(self.0.get(), ino) })
                .ok_or(ENOMEM)?;

            if unsafe { inode.as_ref().i_state & u64::from(bindings::I_NEW) == 0 } {
                // The inode is cached. Just return it.
                //
                // SAFETY: `inode` had its refcount incremented by `iget_locked`; this increment is
                // now owned by `ARef`.
                Ok(Either::Left(unsafe { ARef::from_raw(inode.cast()) }))
            } else {
                Ok(Either::Right(NewINode(unsafe {
                    ARef::from_raw(inode.cast())
                })))
            }
        }

        /// Reads a block from the block device.
        pub fn bread(&self, block: u64) -> Result<ARef<super::buffer::Head>> {
            // Fail requests for non-blockdev file systems. This is a compile-time check.
            match T::SUPER_TYPE {
                Super::BlockDev => {}
                _ => return Err(EIO),
            }

            let ptr =
                ptr::NonNull::new(unsafe { bindings::sb_bread(self.0.get(), block) }).ok_or(EIO)?;
            // SAFETY: `sb_bread` returns a referenced buffer head. Ownership of the increment is
            // passed to the `ARef` instance.
            Ok(unsafe { ARef::from_raw(ptr.cast()) })
        }

        /// Reads `size` bytes starting from `offset` bytes.
        ///
        /// Returns an iterator that returns slices based on blocks.
        pub fn read(
            &self,
            offset: u64,
            size: u64,
        ) -> Result<impl Iterator<Item = Result<super::buffer::View>> + '_> {
            struct BlockIter<'a, T: Type + ?Sized> {
                sb: &'a SuperBlock<T>,
                next_offset: u64,
                end: u64,
            }
            impl<'a, T: Type + ?Sized> Iterator for BlockIter<'a, T> {
                type Item = Result<super::buffer::View>;

                fn next(&mut self) -> Option<Self::Item> {
                    if self.next_offset >= self.end {
                        return None;
                    }

                    let block_size = unsafe { (*self.sb.0.get()).s_blocksize };
                    let bh = match self.sb.bread(self.next_offset / block_size) {
                        Ok(bh) => bh,
                        Err(e) => return Some(Err(e)),
                    };
                    let boffset = self.next_offset & (block_size - 1);
                    let bsize = core::cmp::min(self.end - self.next_offset, block_size - boffset);
                    self.next_offset += bsize;
                    Some(Ok(super::buffer::View::new(
                        bh,
                        boffset as usize,
                        bsize as usize,
                    )))
                }
            }
            Ok(BlockIter {
                sb: self,
                next_offset: offset,
                end: offset.checked_add(size).ok_or(ERANGE)?,
            })
        }

        /// Returns the number of sectors in the underlying block device.
        pub fn sector_count(&self) -> Result<u64> {
            // Fail requests for non-blockdev file systems. This is a compile-time check.
            match T::SUPER_TYPE {
                Super::BlockDev => Ok(unsafe { bindings::bdev_nr_sectors((*self.0.get()).s_bdev) }),
                _ => Err(EIO),
            }
        }
    }

    /// State of [`NewSuperBlock`] that indicates that [`NewSuperBlock::init`] needs to be called
    /// eventually.
    pub struct NeedsInit;

    /// State of [`NewSuperBlock`] that indicates that [`NewSuperBlock::init_data`] needs to be
    /// called eventually.
    pub struct NeedsData;

    /// State of [`NewSuperBlock`] that indicates that [`NewSuperBlock::init_root`] needs to be
    /// called eventually.
    pub struct NeedsRoot;

    /// The type of the inode.
    pub enum INodeType {
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

    /// Time specification.
    pub struct Time {
        /// Number of seconds since the unix epoch.
        pub secs: u64,

        /// Number of nanoseconds within the [`Time::secs`].
        pub nsecs: u64,
    }

    /// Required inode parameters.
    ///
    /// This is used when creating new inodes.
    pub struct INodeParams<T> {
        /// The access mode. It's a mask that grants execute (1), write (2) and read (4) access to
        /// everyone, the owner group, and the owner.
        pub mode: u16,

        /// Type of inode.
        ///
        /// Also carries additional per-type data.
        pub typ: INodeType,

        /// Size of the contents of the inode.
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
        pub ctime: Time,

        /// Last modification time.
        pub mtime: Time,

        /// Last access time.
        pub atime: Time,

        /// Value to attach to this node.
        pub value: T,
    }

    /// Required superblock parameters.
    ///
    /// This is used in [`NewSuperBlock::init`].
    pub struct SuperParams {
        /// The magic number of the superblock.
        pub magic: u32,

        /// The size of a block in powers of 2 (i.e., for a value of `n`, the size is `2^n`).
        pub blocksize_bits: u8,

        /// Maximum size of a file.
        pub maxbytes: i64,

        /// Granularity of c/m/atime in ns (cannot be worse than a second).
        pub time_gran: u32,
    }

    impl SuperParams {
        /// Default value for instances of [`SuperParams`].
        pub const DEFAULT: Self = Self {
            magic: 0,
            blocksize_bits: bindings::PAGE_SIZE as _,
            maxbytes: bindings::MAX_LFS_FILESIZE,
            time_gran: 1,
        };
    }

    /// A superblock that is still being initialised.
    ///
    /// It uses type states to ensure that callers use the right sequence of calls.
    ///
    /// # Invariants
    ///
    /// The superblock is a newly-created one and this is the only active pointer to it.
    pub struct NewSuperBlock<'a, T: Type + ?Sized, S = NeedsInit> {
        sb: &'a mut SuperBlock<T>,

        // This also forces `'a` to be invariant.
        _p: PhantomData<&'a mut &'a S>,
    }

    impl<'a, T: Type + ?Sized> NewSuperBlock<'a, T, NeedsInit> {
        /// Creates a new instance of [`NewSuperBlock`].
        ///
        /// # Safety
        ///
        /// `sb` must point to a newly-created superblock and it must be the only active pointer to
        /// it.
        unsafe fn new(sb: *mut bindings::super_block) -> Self {
            // INVARIANT: The invariants are satisfied by the safety requirements of this function.
            Self {
                // SAFETY: The safety requirements ensure that `sb` is valid for dereference.
                sb: unsafe { &mut *sb.cast() },
                _p: PhantomData,
            }
        }

        /// Initialises the superblock so that it transitions to the [`NeedsData`] type state.
        pub fn init(self, params: &SuperParams) -> Result<NewSuperBlock<'a, T, NeedsData>> {
            // SAFETY: Since this is a new super block, we hold the only reference to it.
            let sb = unsafe { &mut *self.sb.0.get() };

            sb.s_magic = params.magic as _;
            sb.s_op = &Tables::<T>::SUPER_BLOCK;
            sb.s_maxbytes = params.maxbytes;
            sb.s_time_gran = params.time_gran;
            sb.s_blocksize_bits = params.blocksize_bits;
            sb.s_blocksize = 1;
            if sb.s_blocksize.leading_zeros() < params.blocksize_bits.into() {
                return Err(EINVAL);
            }
            sb.s_blocksize = 1 << sb.s_blocksize_bits;
            sb.s_flags |= 1; // TODO: Add constant: bindings::SB_RDONLY;

            Ok(NewSuperBlock {
                sb: self.sb,
                _p: PhantomData,
            })
        }
    }

    impl<'a, T: Type + ?Sized> NewSuperBlock<'a, T, NeedsData> {
        /// Initialises the superblock data.
        pub fn init_data(self, data: T::Data) -> Result<NewSuperBlock<'a, T, NeedsRoot>> {
            let data_ptr = data.into_foreign();
            let guard = ScopeGuard::new(|| {
                unsafe { T::Data::from_foreign(data_ptr) };
            });

            // SAFETY: Since this is a new superblock, we hold the only reference to it.
            let sb = unsafe { &mut *self.sb.0.get() };
            sb.s_fs_info = data_ptr.cast_mut();
            guard.dismiss();

            Ok(NewSuperBlock {
                sb: self.sb,
                _p: PhantomData,
            })
        }

        /// Reads a block from the block device.
        pub fn bread(&self, block: u64) -> Result<ARef<super::buffer::Head>> {
            self.sb.bread(block)
        }

        /// Returns the number of sectors in the underlying block device.
        pub fn sector_count(&self) -> Result<u64> {
            self.sb.sector_count()
        }
    }

    impl<'a, T: Type + ?Sized> NewSuperBlock<'a, T, NeedsRoot> {
        /// Initialises the root of the superblock.
        pub fn init_root(self, inode: ARef<INode<T>>) -> Result<&'a SuperBlock<T>> {
            // SAFETY: The inode is referenced, so it is safe to read the read-only field `i_sb`.
            if unsafe { (*inode.0.get()).i_sb } != self.sb.0.get() {
                return Err(EINVAL);
            }

            // SAFETY: The caller owns a reference to the inode, so it is valid. The reference is
            // transferred to the callee.
            let dentry = unsafe { bindings::d_make_root(ManuallyDrop::new(inode).0.get()) };
            if dentry.is_null() {
                return Err(ENOMEM);
            }

            // SAFETY: Since this is a new superblock, we hold the only reference to it.
            let sb = unsafe { &mut *self.sb.0.get() };
            sb.s_root = dentry;
            Ok(self.sb)
        }

        /// Creates a new inode that is a directory.
        pub fn create_inode(&self, ino: u64) -> Result<NewINode<T>> {
            match self.sb.get_or_create_inode(ino)? {
                Either::Left(_) => Err(EEXIST),
                Either::Right(inode) => Ok(inode),
            }
        }
    }

    impl<'a, T: Type + ?Sized> core::ops::Deref for NewSuperBlock<'a, T, NeedsRoot> {
        type Target = SuperBlock<T>;

        fn deref(&self) -> &Self::Target {
            self.sb
        }
    }

    struct Tables<T: Type + ?Sized>(T);
    impl<T: Type + ?Sized> Tables<T> {
        const CONTEXT: bindings::fs_context_operations = bindings::fs_context_operations {
            free: None,
            parse_param: None,
            get_tree: Some(Self::get_tree_callback),
            reconfigure: None,
            parse_monolithic: None,
            dup: None,
        };

        unsafe extern "C" fn get_tree_callback(fc: *mut bindings::fs_context) -> core::ffi::c_int {
            match T::SUPER_TYPE {
                // SAFETY: `fc` is valid per the callback contract. `fill_super_callback` also has
                // the right type and is a valid callback.
                Super::BlockDev => unsafe {
                    bindings::get_tree_bdev(fc, Some(Self::fill_super_callback))
                },
                // SAFETY: `fc` is valid per the callback contract. `fill_super_callback` also has
                // the right type and is a valid callback.
                Super::Independent => unsafe {
                    bindings::get_tree_nodev(fc, Some(Self::fill_super_callback))
                },
            }
        }

        unsafe extern "C" fn fill_super_callback(
            sb_ptr: *mut bindings::super_block,
            _fc: *mut bindings::fs_context,
        ) -> core::ffi::c_int {
            from_result(|| {
                // SAFETY: The callback contract guarantees that `sb_ptr` is a unique pointer to a
                // newly-created superblock.
                let newsb = unsafe { NewSuperBlock::new(sb_ptr) };
                T::fill_super(newsb)?;
                Ok(0)
            })
        }

        const SUPER_BLOCK: bindings::super_operations = bindings::super_operations {
            alloc_inode: if size_of::<T::INodeData>() != 0 {
                Some(Self::alloc_inode_callback)
            } else {
                None
            },
            // TODO: If we have a zero-sized type with a Drop implementation, we want to implement
            // destroy_inode.
            destroy_inode: if size_of::<T::INodeData>() != 0 {
                Some(Self::destroy_inode_callback)
            } else {
                None
            },
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

        unsafe extern "C" fn alloc_inode_callback(
            sb: *mut bindings::super_block,
        ) -> *mut bindings::inode {
            // SAFETY: The callback contract guarantees that `sb` is valid for read.
            let super_type = unsafe { (*sb).s_type };

            // SAFETY: This callback is only used in `Registration`, so `super_type` is necessarily
            // embedded in a `Registration`, which is guaranteed to be valid because it has a
            // superblock associated to it.
            let reg = unsafe { &*container_of!(super_type, Registration, fs) };

            // SAFETY: `sb` and `cache` are guaranteed to be valid by the callback contract and by
            // the existence of a superblock respectively.
            let ptr = unsafe {
                bindings::alloc_inode_sb(sb, MemCache::ptr(&reg.inode_cache), bindings::GFP_KERNEL)
            }
            .cast::<INodeWithData<T::INodeData>>();
            if ptr.is_null() {
                return ptr::null_mut();
            }
            ptr::addr_of_mut!((*ptr).inode)
        }

        unsafe extern "C" fn destroy_inode_callback(inode: *mut bindings::inode) {
            // SAFETY: By the C contrat, inode is a valid pointer.
            let is_bad = unsafe { bindings::is_bad_inode(inode) };

            // SAFETY: The inode is guaranteed to be valid by the callback contract. Additionally, the
            // superblock is also guaranteed to still be valid by the inode existence.
            let super_type = unsafe { (*(*inode).i_sb).s_type };

            // SAFETY: This callback is only used in `Registration`, so `super_type` is necessarily
            // embedded in a `Registration`, which is guaranteed to be valid because it has a
            // superblock associated to it.
            let reg = unsafe { &*container_of!(super_type, Registration, fs) };
            let ptr = container_of!(inode, INodeWithData<T::INodeData>, inode).cast_mut();

            if !is_bad {
                // SAFETY: The code either initialises the data or marks the inode as bad, since
                // it's not bad, it's safey to drop it here.
                unsafe { ptr::drop_in_place((*ptr).data.as_mut_ptr()) };
            }

            // The callback contract guarantees that the inode was previously allocated via the
            // `alloc_inode_callback` callback, so it is safe to free it back to the cache.
            unsafe { bindings::kmem_cache_free(MemCache::ptr(&reg.inode_cache), ptr.cast()) };
        }

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
                let inode = unsafe { &*(*file).f_inode.cast::<INode<T>>() };
                let ctx = unsafe { &mut *ctx_ptr };
                let new_pos = T::read_dir(inode, ctx.pos, |name, foffset, ino, typ| {
                    let Ok(name_len) = i32::try_from(name.len()) else {
                        return false;
                    };
                    let Some(actor) = ctx.actor else {
                        return false;
                    };

                    unsafe { actor(ctx, name.as_ptr().cast(), name_len, foffset, ino, typ as _) }
                })?;
                ctx.pos = new_pos;
                Ok(0)
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
        };

        extern "C" fn lookup_callback(
            parent_ptr: *mut bindings::inode,
            dentry: *mut bindings::dentry,
            _flags: u32,
        ) -> *mut bindings::dentry {
            let parent = unsafe { &*parent_ptr.cast::<INode<T>>() };
            let Ok(name_len) = usize::try_from(unsafe { (*dentry).d_name.__bindgen_anon_1.__bindgen_anon_1.len}) else {
                return ENOENT.to_ptr();
            };
            let name = unsafe { core::slice::from_raw_parts((*dentry).d_name.name, name_len) };
            match T::lookup(parent, name) {
                Err(e) => e.to_ptr(),
                Ok(inode) => unsafe {
                    bindings::d_splice_alias(ManuallyDrop::new(inode).0.get(), dentry)
                },
            }
        }

        const LNK_INODE_OPERATIONS: bindings::inode_operations = bindings::inode_operations {
            lookup: None,
            get_link: Some(bindings::page_get_link),
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
        };

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
                // SAFETY: The C contract guarantees that the folio is valid and locked, with
                // ownership of the lock transferred to the callee (us). The folio is also
                // guaranteed not to outlive this function.
                T::read_folio(inode, unsafe { LockedFolio::from_raw(folio) })?;
                Ok(0)
            })
        }
    }

    /// Kernel module that exposes a single read-only file system implemented by `T`.
    #[pin_data]
    pub struct Module<T: Type + ?Sized> {
        #[pin]
        fs_reg: Registration,
        _p: PhantomData<T>,
    }

    impl<T: Type + ?Sized + Sync + Send> crate::InPlaceModule for Module<T> {
        type Init = impl PinInit<Self, Error>;
        fn init(module: &'static ThisModule) -> Result<Self::Init> {
            Ok(try_pin_init!(Self {
                fs_reg <- Registration::new::<T>(module),
                _p: PhantomData,
            }))
        }
    }

    // TODO: Update sample.
    /// Declares a kernel module that exposes a single file system.
    ///
    /// The `type` argument must be a type which implements the [`Type`] trait. Also accepts various
    /// forms of kernel metadata.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use kernel::prelude::*;
    /// use kernel::{c_str, fs};
    ///
    /// module_fs! {
    ///     type: MyFs,
    ///     name: b"my_fs_kernel_module",
    ///     author: b"Rust for Linux Contributors",
    ///     description: b"My very own file system kernel module!",
    ///     license: b"GPL",
    /// }
    ///
    /// struct MyFs;
    ///
    /// impl fs::Type for MyFs {
    ///     const SUPER_TYPE: fs::Super = fs::Super::Independent;
    ///     const NAME: &'static CStr = c_str!("example");
    ///     const FLAGS: i32 = 0;
    ///
    ///     fn fill_super(_data: (), sb: fs::NewSuperBlock<'_, Self>) -> Result<&fs::SuperBlock<Self>> {
    ///         let sb = sb.init(
    ///             (),
    ///             &fs::SuperParams {
    ///                 magic: 0x6578616d,
    ///                 ..fs::SuperParams::DEFAULT
    ///             },
    ///         )?;
    ///         let root_inode = sb.try_new_dcache_dir_inode(fs::INodeParams {
    ///             mode: 0o755,
    ///             ino: 1,
    ///             value: (),
    ///         })?;
    ///         let root = sb.try_new_root_dentry(root_inode)?;
    ///         let sb = sb.init_root(root)?;
    ///         Ok(sb)
    ///     }
    /// }
    /// ```
    #[macro_export]
    macro_rules! module_ro_fs {
        (type: $type:ty, $($f:tt)*) => {
            type ModuleType = $crate::fs::ro::Module<$type>;
            $crate::macros::module! {
                type: ModuleType,
                $($f)*
            }
        }
    }
}
