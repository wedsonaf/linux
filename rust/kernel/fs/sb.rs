// SPDX-License-Identifier: GPL-2.0

//! File system super blocks.
//!
//! This module allows Rust code to use superblocks.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::inode::{self, INode, Ino};
use super::{buffer, FileSystem, Offset};
use crate::error::{code::*, to_result, Result};
use crate::types::{ARef, Either, ForeignOwnable, Opaque, ScopeGuard};
use crate::{bindings, block, build_error, folio::UniqueFolio};
use core::{marker::PhantomData, ptr};

/// Type of superblock keying.
///
/// It determines how C's `fs_context_operations::get_tree` is implemented.
pub enum Type {
    /// Multiple independent superblocks may exist.
    Independent,

    /// Uses a block device.
    BlockDev,
}

/// A typestate for [`SuperBlock`] that indicates that it's a new one, so not fully initialized
/// yet.
pub struct New;

/// A typestate for [`SuperBlock`] that indicates that it's ready to be used.
pub struct Ready;

// SAFETY: Instances of `SuperBlock<T, Ready>` are only created after initialising the data.
unsafe impl DataInited for Ready {}

/// Indicates that a superblock in this typestate has data initialized.
///
/// # Safety
///
/// Implementers must ensure that `s_fs_info` is properly initialised in this state.
#[doc(hidden)]
pub unsafe trait DataInited {}

/// A file system super block.
///
/// Wraps the kernel's `struct super_block`.
#[repr(transparent)]
pub struct SuperBlock<T: FileSystem + ?Sized, S = Ready>(
    pub(crate) Opaque<bindings::super_block>,
    PhantomData<(S, T)>,
);

impl<T: FileSystem + ?Sized, S> SuperBlock<T, S> {
    /// Creates a new superblock reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    ///
    /// * `ptr` is valid and remains so for the lifetime of the returned object.
    /// * `ptr` has the correct file system type, or `T` is [`super::UnspecifiedFS`].
    /// * `ptr` in the right typestate.
    pub(crate) unsafe fn from_raw<'a>(ptr: *mut bindings::super_block) -> &'a Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &*ptr.cast::<Self>() }
    }

    /// Tries to get an existing inode or create a new one if it doesn't exist yet.
    pub fn get_or_create_inode(&self, ino: Ino) -> Result<Either<ARef<INode<T>>, inode::New<T>>> {
        // SAFETY: All superblock-related state needed by `iget_locked` is initialised by C code
        // before calling `fill_super_callback`, or by `fill_super_callback` itself before calling
        // `super_params`, which is the first function to see a new superblock.
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
            // `inode::New`.
            Ok(Either::Right(inode::New(inode, PhantomData)))
        }
    }

    /// Reads a block from the block device.
    #[cfg(CONFIG_BUFFER_HEAD)]
    pub fn bread(&self, block: u64) -> Result<ARef<buffer::Head>> {
        // Fail requests for non-blockdev file systems. This is a compile-time check.
        match T::SUPER_TYPE {
            Type::BlockDev => {}
            _ => build_error!("bread is only available in blockdev superblocks"),
        }

        // SAFETY: This function is only valid after the `NeedsInit` typestate, so the block size
        // is known and the superblock can be used to read blocks.
        let ptr =
            ptr::NonNull::new(unsafe { bindings::sb_bread(self.0.get(), block) }).ok_or(EIO)?;
        // SAFETY: `sb_bread` returns a referenced buffer head. Ownership of the increment is
        // passed to the `ARef` instance.
        Ok(unsafe { ARef::from_raw(ptr.cast::<buffer::Head>()) })
    }

    /// Reads `size` bytes starting from `offset` bytes.
    ///
    /// Returns an iterator that returns slices based on blocks.
    #[cfg(CONFIG_BUFFER_HEAD)]
    pub fn read(
        &self,
        offset: u64,
        size: u64,
    ) -> Result<impl Iterator<Item = Result<buffer::View>> + '_> {
        struct BlockIter<'a, T: FileSystem + ?Sized, S> {
            sb: &'a SuperBlock<T, S>,
            next_offset: u64,
            end: u64,
        }
        impl<'a, T: FileSystem + ?Sized, S> Iterator for BlockIter<'a, T, S> {
            type Item = Result<buffer::View>;

            fn next(&mut self) -> Option<Self::Item> {
                if self.next_offset >= self.end {
                    return None;
                }

                // SAFETY: The superblock is valid and has had its block size initialised.
                let block_size = unsafe { (*self.sb.0.get()).s_blocksize };
                let bh = match self.sb.bread(self.next_offset / block_size) {
                    Ok(bh) => bh,
                    Err(e) => return Some(Err(e)),
                };
                let boffset = self.next_offset & (block_size - 1);
                let bsize = core::cmp::min(self.end - self.next_offset, block_size - boffset);
                self.next_offset += bsize;
                Some(Ok(buffer::View::new(bh, boffset as usize, bsize as usize)))
            }
        }
        Ok(BlockIter {
            sb: self,
            next_offset: offset,
            end: offset.checked_add(size).ok_or(ERANGE)?,
        })
    }

    /// Returns the block device associated with the superblock.
    pub fn bdev(&self) -> &block::Device {
        // Fail requests for non-blockdev file systems. This is a compile-time check.
        match T::SUPER_TYPE {
            // The superblock is valid and given that it's a blockdev superblock it must have a
            // valid `s_bdev`.
            Type::BlockDev => {}
            _ => build_error!("bdev is only available in blockdev superblocks"),
        }

        // SAFETY: The superblock is valid and given that it's a blockdev superblock it must have a
        // valid `s_bdev` that remain valid while the superblock (`self`) is valid.
        unsafe { block::Device::from_raw((*self.0.get()).s_bdev) }
    }

    /// Reads sectors.
    ///
    /// `count` must be such that the total size doesn't exceed a page.
    pub fn sread(&self, sector: u64, count: usize, folio: &mut UniqueFolio) -> Result {
        // Fail requests for non-blockdev file systems. This is a compile-time check.
        match T::SUPER_TYPE {
            // The superblock is valid and given that it's a blockdev superblock it must have a
            // valid `s_bdev`.
            Type::BlockDev => {}
            _ => build_error!("sread is only available in blockdev superblocks"),
        }

        // Read the sectors.
        let mut bio = bindings::bio::default();
        let bvec = Opaque::<bindings::bio_vec>::uninit();
        let bdev = self.bdev().0.get();

        // SAFETY: `bio` and `bvec` are allocated on the stack, they're both valid. `bdev` is valid
        // because we checked that this is `BlockDev` filesystem.
        unsafe { bindings::bio_init(&mut bio, bdev, bvec.get(), 1, bindings::req_op_REQ_OP_READ) };

        // SAFETY: `bio` was just initialised with `bio_init` above, so it's safe to call
        // `bio_uninit` on the way out.
        let mut bio =
            ScopeGuard::new_with_data(bio, |mut b| unsafe { bindings::bio_uninit(&mut b) });

        crate::build_assert!(count * (bindings::SECTOR_SIZE as usize) <= bindings::PAGE_SIZE);

        // SAFETY: We have one free `bvec` (initialsied above). We also know that size won't exceed
        // a page size (build_assert above).
        unsafe {
            bindings::bio_add_folio_nofail(
                &mut *bio,
                folio.0 .0.get(),
                count * (bindings::SECTOR_SIZE as usize),
                0,
            )
        };
        bio.bi_iter.bi_sector = sector;

        // SAFETY: The bio was fully initialised above.
        to_result(unsafe { bindings::submit_bio_wait(&mut *bio) })?;
        Ok(())
    }

    /// Returns the number of sectors in the underlying block device.
    pub fn sector_count(&self) -> u64 {
        // Fail requests for non-blockdev file systems. This is a compile-time check.
        match T::SUPER_TYPE {
            // SAFETY: The superblock is valid and given that it's a blockdev superblock it must
            // have a valid `s_bdev`.
            Type::BlockDev => unsafe { bindings::bdev_nr_sectors((*self.0.get()).s_bdev) },
            _ => build_error!("sector_count is only available in blockdev superblocks"),
        }
    }
}

impl<T: FileSystem + ?Sized, S: DataInited> SuperBlock<T, S> {
    /// Returns the data associated with the superblock.
    pub fn data(&self) -> <T::Data as ForeignOwnable>::Borrowed<'_> {
        if T::IS_UNSPECIFIED {
            crate::build_error!("super block data type is unspecified");
        }

        // SAFETY: This method is only available if the typestate implements `DataInited`, whose
        // safety requirements include `s_fs_info` being properly initialised.
        let ptr = unsafe { (*self.0.get()).s_fs_info };
        unsafe { T::Data::borrow(ptr) }
    }
}

/// Required superblock parameters.
///
/// This is returned by implementations of [`FileSystem::super_params`].
pub struct Params<T: ForeignOwnable + Send + Sync> {
    /// The magic number of the superblock.
    pub magic: u32,

    /// The size of a block in powers of 2 (i.e., for a value of `n`, the size is `2^n`).
    pub blocksize_bits: u8,

    /// Maximum size of a file.
    ///
    /// The maximum allowed value is [`super::MAX_LFS_FILESIZE`].
    pub maxbytes: Offset,

    /// Granularity of c/m/atime in ns (cannot be worse than a second).
    pub time_gran: u32,

    /// Data to be associated with the superblock.
    pub data: T,
}
