//! Block devices.
//!
//! This module allows Rust code to use block devices.
//!
//! C headers: [`include/linux/blk_types.h`](../../include/linux/blk_types.h)

use crate::bindings;
use crate::types::Opaque;

/// A block device.
///
/// Wraps the kernel's `struct block_device`.
#[repr(transparent)]
pub struct Device(pub(crate) Opaque<bindings::block_device>);

impl Device {
    /// Creates a new block device reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that `ptr` is valid and remains so for the lifetime of the returned
    /// object.
    #[allow(dead_code)]
    pub(crate) unsafe fn from_raw<'a>(ptr: *mut bindings::block_device) -> &'a Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &*ptr.cast::<Self>() }
    }
}
