// SPDX-License-Identifier: GPL-2.0

//! Networking core.
//!
//! C headers: [`include/net/net_namespace.h`](../../../../include/linux/net/net_namespace.h),
//! [`include/linux/netdevice.h`](../../../../include/linux/netdevice.h),
//! [`include/linux/skbuff.h`](../../../../include/linux/skbuff.h).

use crate::{bindings, str::CStr, ARef, AlwaysRefCounted};
use core::{cell::UnsafeCell, ptr::NonNull};

pub mod filter;

/// Wraps the kernel's `struct net_device`.
#[repr(transparent)]
pub struct Device(UnsafeCell<bindings::net_device>);

// SAFETY: Instances of `Device` are created on the C side. They are always refcounted.
unsafe impl AlwaysRefCounted for Device {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::dev_hold(self.0.get()) };
    }

    unsafe fn dec_ref(obj: core::ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::dev_put(obj.cast().as_ptr()) };
    }
}

/// Wraps the kernel's `struct net`.
#[repr(transparent)]
pub struct Namespace(UnsafeCell<bindings::net>);

impl Namespace {
    /// Finds a network device with the given name in the namespace.
    pub fn dev_get_by_name(&self, name: &CStr) -> Option<ARef<Device>> {
        // SAFETY: The existence of a shared reference guarantees the refcount is nonzero.
        let ptr =
            NonNull::new(unsafe { bindings::dev_get_by_name(self.0.get(), name.as_char_ptr()) })?;
        Some(unsafe { ARef::from_raw(ptr.cast()) })
    }
}

// SAFETY: Instances of `Namespace` are created on the C side. They are always refcounted.
unsafe impl AlwaysRefCounted for Namespace {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::get_net(self.0.get()) };
    }

    unsafe fn dec_ref(obj: core::ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::put_net(obj.cast().as_ptr()) };
    }
}

/// Returns the network namspace for the `init` process.
pub fn init_ns() -> &'static Namespace {
    unsafe { &*core::ptr::addr_of!(bindings::init_net).cast() }
}

/// Wraps the kernel's `struct sk_buff`.
#[repr(transparent)]
pub struct SkBuff(UnsafeCell<bindings::sk_buff>);

impl SkBuff {
    /// Creates a reference to an [`SkBuff`] from a valid pointer.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `ptr` is valid and remains valid for the lifetime of the
    /// returned [`SkbBuff`] instance.
    pub(crate) unsafe fn from_ptr<'a>(ptr: *const bindings::sk_buff) -> &'a SkBuff {
        // SAFETY: The safety requirements guarantee the validity of the dereference, while the
        // `SkBuff` type being transparent makes the cast ok.
        unsafe { &*ptr.cast() }
    }

    /// Returns the remaining data in the buffer's first segment.
    pub fn head_data(&self) -> &[u8] {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        let headlen = unsafe { bindings::skb_headlen(self.0.get()) };
        let len = headlen.try_into().unwrap_or(usize::MAX);
        // SAFETY: The existence of a shared reference means `self.0` is valid.
        let data = unsafe { core::ptr::addr_of!((*self.0.get()).data).read() };
        // SAFETY: The `struct sk_buff` conventions guarantee that at least `skb_headlen(skb)` bytes
        // are valid from `skb->data`.
        unsafe { core::slice::from_raw_parts(data, len) }
    }
}

// SAFETY: Instances of `SkBuff` are created on the C side. They are always refcounted.
unsafe impl AlwaysRefCounted for SkBuff {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::skb_get(self.0.get()) };
    }

    unsafe fn dec_ref(obj: core::ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe {
            bindings::kfree_skb_reason(
                obj.cast().as_ptr(),
                bindings::skb_drop_reason_SKB_DROP_REASON_NOT_SPECIFIED,
            )
        };
    }
}
