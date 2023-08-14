// SPDX-License-Identifier: GPL-2.0

//! Groups of contiguous pages, folios.
//!
//! C headers: [`include/linux/fs.h`](../../include/linux/fs.h)

use crate::error::{code::*, Result};
use crate::types::{AlwaysRefCounted, Opaque, ScopeGuard};
use core::{cmp::min, ptr};

/// Wraps the kernel's `struct folio`.
///
/// # Invariants
///
/// Instances of this type are always ref-counted, that is, a call to `folio_get` ensures that the
/// allocation remains valid at least until the matching call to `folio_put`.
#[repr(transparent)]
pub struct Folio(Opaque<bindings::folio>);

// SAFETY: The type invariants guarantee that `Folio` is always ref-counted.
unsafe impl AlwaysRefCounted for Folio {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::folio_get(self.0.get()) };
    }

    unsafe fn dec_ref(obj: ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::folio_put(obj.cast().as_ptr()) }
    }
}

impl Folio {
    /// Returns the byte position of this folio in its file.
    pub fn pos(&self) -> i64 {
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
}

/// A locked [`Folio`].
pub struct LockedFolio<'a>(&'a Folio);

impl LockedFolio<'_> {
    /// Creates a new locked folio from a raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that the folio is valid and locked. Additionally, that the
    /// responsibility of unlocking is transferred to the new instance of [`LockedFolio`]. Lastly,
    /// that the returned [`LockedFolio`] doesn't outlive the refcount that keeps it alive.
    #[allow(dead_code)]
    pub(crate) unsafe fn from_raw(folio: *const bindings::folio) -> Self {
        unsafe { Self(&*folio.cast()) }
    }

    /// Marks the folio as being up to date.
    pub fn mark_uptodate(&mut self) {
        // SAFETY: The folio is valid because the shared reference implies a non-zero refcount.
        unsafe { bindings::folio_mark_uptodate(self.0 .0.get()) }
    }

    /// Sets the error flag on the folio.
    pub fn set_error(&mut self) {
        // SAFETY: The folio is valid because the shared reference implies a non-zero refcount.
        unsafe { bindings::folio_set_error(self.0 .0.get()) }
    }

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
        if end > self.size() {
            return Err(EINVAL);
        }

        while remaining > 0 {
            let page_offset = next_offset & (bindings::PAGE_SIZE - 1);
            let usable = min(remaining, bindings::PAGE_SIZE - page_offset);
            let ptr = unsafe { bindings::kmap_local_folio(self.0 .0.get(), next_offset) };
            let _guard = ScopeGuard::new(|| unsafe { bindings::kunmap_local(ptr) });
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

impl core::ops::Deref for LockedFolio<'_> {
    type Target = Folio;
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl Drop for LockedFolio<'_> {
    fn drop(&mut self) {
        // SAFETY: The folio is valid because the shared reference implies a non-zero refcount.
        unsafe { bindings::folio_unlock(self.0 .0.get()) }
    }
}
