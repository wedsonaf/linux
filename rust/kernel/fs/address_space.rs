// SPDX-License-Identifier: GPL-2.0

//! File system address spaces.
//!
//! This module allows Rust code implement address space operations.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::{file::File, FileSystem};
use crate::error::{from_result, Result};
use crate::{bindings, folio::Folio, folio::PageCache, types::Locked};
use core::marker::PhantomData;
use macros::vtable;

/// Operations implemented by address spaces.
#[vtable]
pub trait Operations {
    /// File system that these operations are compatible with.
    type FileSystem: FileSystem + ?Sized;

    /// Reads the contents of the inode into the given folio.
    fn read_folio(
        file: Option<&File<Self::FileSystem>>,
        folio: Locked<&Folio<PageCache<Self::FileSystem>>>,
    ) -> Result;
}

/// Represents address space operations.
pub struct Ops<T: FileSystem + ?Sized>(
    pub(crate) *const bindings::address_space_operations,
    pub(crate) PhantomData<T>,
);

impl<T: FileSystem + ?Sized> Ops<T> {
    /// Creates the address space operations from a type that implements the [`Operations`] trait.
    pub const fn new<U: Operations<FileSystem = T> + ?Sized>() -> Self {
        struct Table<T: Operations + ?Sized>(PhantomData<T>);
        impl<T: Operations + ?Sized> Table<T> {
            const TABLE: bindings::address_space_operations = bindings::address_space_operations {
                writepage: None,
                read_folio: if T::HAS_READ_FOLIO {
                    Some(Self::read_folio_callback)
                } else {
                    None
                },
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
                error_remove_folio: None,
                swap_activate: None,
                swap_deactivate: None,
                swap_rw: None,
            };

            extern "C" fn read_folio_callback(
                file_ptr: *mut bindings::file,
                folio_ptr: *mut bindings::folio,
            ) -> i32 {
                from_result(|| {
                    let file = if file_ptr.is_null() {
                        None
                    } else {
                        // SAFETY: The C API guarantees that `file_ptr` is a valid file if non-null.
                        Some(unsafe { File::from_raw(file_ptr) })
                    };

                    // SAFETY: The C API guarantees that `folio_ptr` is a valid folio.
                    let folio = unsafe { Folio::from_raw(folio_ptr) };

                    // SAFETY: The C contract guarantees that the folio is valid and locked, with
                    // ownership of the lock transferred to the callee (this function).
                    T::read_folio(file, unsafe { Locked::new(folio) })?;
                    Ok(0)
                })
            }
        }
        Self(&Table::<U>::TABLE, PhantomData)
    }
}
