// SPDX-License-Identifier: GPL-2.0

//! File system address spaces.
//!
//! This module allows Rust code implement address space operations.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::FileSystem;
use crate::bindings;
use core::marker::PhantomData;
use macros::vtable;

/// Operations implemented by address spaces.
#[vtable]
pub trait Operations {
    /// File system that these operations are compatible with.
    type FileSystem: FileSystem + ?Sized;
}

/// Represents address space operations.
#[allow(dead_code)]
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
                read_folio: None,
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
        }
        Self(&Table::<U>::TABLE, PhantomData)
    }
}
