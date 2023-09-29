// SPDX-License-Identifier: GPL-2.0

//! Groups of contiguous pages, folios.
//!
//! C headers: [`include/linux/mm.h`](srctree/include/linux/mm.h)

use crate::error::{code::*, Result};
use crate::fs::{self, inode::INode, FileSystem};
use crate::types::{self, ARef, AlwaysRefCounted, Locked, Opaque, ScopeGuard};
use core::{cmp::min, marker::PhantomData, ops::Deref, ptr};

/// The type of a [`Folio`] is unspecified.
pub struct Unspecified;

/// The [`Folio`] instance is a page-cache one.
pub struct PageCache<T: FileSystem + ?Sized>(PhantomData<T>);

/// A folio.
///
/// The `S` type parameter specifies the type of folio.
///
/// Wraps the kernel's `struct folio`.
///
/// # Invariants
///
/// Instances of this type are always ref-counted, that is, a call to `folio_get` ensures that the
/// allocation remains valid at least until the matching call to `folio_put`.
#[repr(transparent)]
pub struct Folio<S = Unspecified>(pub(crate) Opaque<bindings::folio>, PhantomData<S>);

// SAFETY: The type invariants guarantee that `Folio` is always ref-counted.
unsafe impl<S> AlwaysRefCounted for Folio<S> {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::folio_get(self.0.get()) };
    }

    unsafe fn dec_ref(obj: ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::folio_put(obj.as_ref().0.get()) }
    }
}

impl<S> Folio<S> {
    /// Creates a new folio reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    /// * `ptr` is valid and remains so for the lifetime of the returned reference.
    /// * The folio has the right state.
    #[allow(dead_code)]
    pub(crate) unsafe fn from_raw<'a>(ptr: *mut bindings::folio) -> &'a Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &*ptr.cast::<Self>() }
    }

    /// Returns the byte position of this folio in its file.
    pub fn pos(&self) -> fs::Offset {
        // SAFETY: The folio is valid because the shared reference implies a non-zero refcount.
        unsafe { bindings::folio_pos(self.0.get()) }
    }

    /// Returns the byte size of this folio.
    pub fn size(&self) -> usize {
        // SAFETY: The folio is valid because the shared reference implies a non-zero refcount.
        unsafe { bindings::folio_size(self.0.get()) }
    }

    /// Flushes the data cache for the pages that make up the folio.
    pub fn flush_dcache(&self) {
        // SAFETY: The folio is valid because the shared reference implies a non-zero refcount.
        unsafe { bindings::flush_dcache_folio(self.0.get()) }
    }

    /// Returns true if the folio is in highmem.
    pub fn test_highmem(&self) -> bool {
        // SAFETY: The folio is valid because the shared reference implies a non-zero refcount.
        unsafe { bindings::folio_test_highmem(self.0.get()) }
    }

    /// Consumes the folio and returns an owned mapped reference.
    ///
    /// # Safety
    ///
    /// Callers must ensure that the folio is not concurrently mapped for write.
    pub unsafe fn map_owned(folio: ARef<Self>, offset: usize) -> Result<Mapped<'static, S>> {
        // SAFETY: The safety requirements of this function satisfy those of `map`.
        let guard = unsafe { folio.map(offset)? };
        let to_unmap = guard.page;
        let data = &guard[0] as *const u8;
        let data_len = guard.len();
        core::mem::forget(guard);
        Ok(Mapped {
            _folio: folio,
            to_unmap,
            data,
            data_len,
            _p: PhantomData,
        })
    }

    /// Maps the contents of a folio page into a slice.
    ///
    /// # Safety
    ///
    /// Callers must ensure that the folio is not concurrently mapped for write.
    pub unsafe fn map(&self, offset: usize) -> Result<MapGuard<'_>> {
        if offset >= self.size() {
            return Err(EDOM);
        }

        let page_index = offset / bindings::PAGE_SIZE;
        let page_offset = offset % bindings::PAGE_SIZE;

        // SAFETY: We just checked that the index is within bounds of the folio.
        let page = unsafe { bindings::folio_page(self.0.get(), page_index) };

        // SAFETY: `page` is valid because it was returned by `folio_page` above.
        let ptr = unsafe { bindings::kmap(page) };

        let size = if self.test_highmem() {
            bindings::PAGE_SIZE
        } else {
            self.size()
        };

        // SAFETY: We just mapped `ptr`, so it's valid for read.
        let data = unsafe {
            core::slice::from_raw_parts(ptr.cast::<u8>().add(page_offset), size - page_offset)
        };
        Ok(MapGuard { data, page })
    }
}

impl<T: FileSystem + ?Sized> Folio<PageCache<T>> {
    /// Returns the inode for which this folio holds data.
    pub fn inode(&self) -> &INode<T> {
        // SAFETY: The type parameter guarantees that this is a page-cache folio, so host is
        // populated.
        unsafe {
            INode::from_raw((*(*self.0.get()).__bindgen_anon_1.__bindgen_anon_1.mapping).host)
        }
    }
}

/// An owned mapped folio.
///
/// That is, a mapped version of a folio that holds a reference to it.
///
/// The lifetime is used to tie the mapping to other lifetime, for example, the lifetime of a lock
/// guard. This allows the mapping to exist only while a lock is held.
///
/// # Invariants
///
/// `to_unmap` is a mapped page of the folio. The byte range starting at `data` and extending for
/// `data_len` bytes is within the mapped page.
pub struct Mapped<'a, S = Unspecified> {
    _folio: ARef<Folio<S>>,
    to_unmap: *mut bindings::page,
    data: *const u8,
    data_len: usize,
    _p: PhantomData<&'a ()>,
}

impl<S> Mapped<'_, S> {
    /// Limits the length of the mapped region.
    pub fn cap_len(&mut self, new_len: usize) {
        if new_len < self.data_len {
            self.data_len = new_len;
        }
    }
}

impl<S> Deref for Mapped<'_, S> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        // SAFETY: By the type invariant, we know that `data` and `data_len` form a valid slice.
        unsafe { core::slice::from_raw_parts(self.data, self.data_len) }
    }
}

impl<S> Drop for Mapped<'_, S> {
    fn drop(&mut self) {
        // SAFETY: By the type invariant, we know that `to_unmap` is mapped.
        unsafe { bindings::kunmap(self.to_unmap) };
    }
}

/// A mapped [`Folio`].
pub struct MapGuard<'a> {
    data: &'a [u8],
    page: *mut bindings::page,
}

impl Deref for MapGuard<'_> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.data
    }
}

impl Drop for MapGuard<'_> {
    fn drop(&mut self) {
        // SAFETY: A `MapGuard` instance is only created when `kmap` succeeds, so it's ok to unmap
        // it when the guard is dropped.
        unsafe { bindings::kunmap(self.page) };
    }
}

// SAFETY: `raw_lock` calls folio_lock, which actually locks the folio.
unsafe impl<S> types::Lockable for Folio<S> {
    fn raw_lock(&self) {
        // SAFETY: The folio is valid because the shared reference implies a non-zero refcount.
        unsafe { bindings::folio_lock(self.0.get()) }
    }

    unsafe fn unlock(&self) {
        // SAFETY: The safety requirements guarantee that the folio is locked.
        unsafe { bindings::folio_unlock(self.0.get()) }
    }
}

impl<T: Deref<Target = Folio<S>>, S> Locked<T> {
    /// Marks the folio as being up to date.
    pub fn mark_uptodate(&mut self) {
        // SAFETY: The folio is valid because the shared reference implies a non-zero refcount.
        unsafe { bindings::folio_mark_uptodate(self.deref().0.get()) }
    }

    // TODO: What prevents someone who doesn't have the folio locked from calling this?
    fn for_each_page(
        &mut self,
        offset: usize,
        len: usize,
        mut cb: impl FnMut(&mut [u8]) -> Result,
    ) -> Result {
        let mut remaining = len;
        let mut next_offset = offset;

        // Check that we don't overflow the folio.
        let end = offset.checked_add(len).ok_or(EDOM)?;
        if end > self.deref().size() {
            return Err(EINVAL);
        }

        while remaining > 0 {
            let map_size = if self.test_highmem() {
                bindings::PAGE_SIZE - (next_offset & (bindings::PAGE_SIZE - 1))
            } else {
                self.size() - next_offset
            };
            let usable = min(remaining, map_size);
            // SAFETY: The folio is valid because the shared reference implies a non-zero refcount;
            // `next_offset` is also guaranteed be lesss than the folio size.
            let ptr = unsafe { bindings::kmap_local_folio(self.deref().0.get(), next_offset) };

            // SAFETY: `ptr` was just returned by the `kmap_local_folio` above.
            let _guard = ScopeGuard::new(|| unsafe { bindings::kunmap_local(ptr) });

            // SAFETY: `kmap_local_folio` maps whole page so we know it's mapped for at least
            // `usable` bytes.
            let s = unsafe { core::slice::from_raw_parts_mut(ptr.cast::<u8>(), usable) };
            cb(s)?;

            next_offset += usable;
            remaining -= usable;
        }

        Ok(())
    }

    /// Writes the given slice into the folio.
    pub fn write(&mut self, offset: usize, data: &[u8]) -> Result {
        let mut remaining = data;

        self.for_each_page(offset, data.len(), |s| {
            s.copy_from_slice(&remaining[..s.len()]);
            remaining = &remaining[s.len()..];
            Ok(())
        })
    }

    /// Writes zeroes into the folio.
    pub fn zero_out(&mut self, offset: usize, len: usize) -> Result {
        self.for_each_page(offset, len, |s| {
            s.fill(0);
            Ok(())
        })
    }
}
