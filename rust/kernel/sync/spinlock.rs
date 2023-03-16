// SPDX-License-Identifier: GPL-2.0

//! A kernel spinlock.
//!
//! This module allows Rust code to use the kernel's [`struct spinlock`].

use super::{Guard, Lock, LockClassKey};
use crate::{bindings, init::PinInit, pin_init, str::CStr, types::Opaque};
use core::{cell::UnsafeCell, marker::PhantomPinned};
use macros::pin_data;

/// Creates a [`SpinLock`] initialiser with the given name and a newly-created lock class.
#[macro_export]
macro_rules! new_spinlock {
    ($inner:expr, $name:literal) => {{
        let name = $crate::c_str!($name);
        $crate::sync::SpinLock::new($inner, name, $crate::static_lock_class!())
    }};
}

/// Exposes the kernel's [`spinlock_t`]. When multiple CPUs attempt to lock the same spinlock, only
/// one at a time is allowed to progress, the others will block (spinning) until the spinlock is
/// unlocked, at which point another CPU will be allowed to make progress.
///
/// # Examples
///
/// The following example shows how to declare, allocate and initialise a struct (`Example`) that
/// contains an inner struct (`Inner`) that is protected by a spinlock.
///
/// ```
/// use kernel::{init::InPlaceInit, init::PinInit, new_spinlock, pin_init, sync::SpinLock};
///
/// struct Inner {
///     a: u32,
///     b: u32,
/// }
///
/// #[pin_data]
/// struct Example {
///     c: u32,
///     #[pin]
///     d: SpinLock<Inner>,
/// }
///
/// impl Example {
///     fn new() -> impl PinInit<Self> {
///         pin_init!(Self {
///             c: 10,
///             d <- new_spinlock!(Inner { a: 20, b: 30 }, "Example::d"),
///         })
///     }
/// }
///
/// // Allocate a boxed `Example`.
/// let e = Box::pin_init(Example::new())?;
/// assert_eq!(e.c, 10);
/// assert_eq!(e.d.lock().a, 20);
/// assert_eq!(e.d.lock().b, 30);
/// ```
///
/// The following example shows how to use interior mutability to modify the contents of a struct
/// protected by a spinlock despite only having a shared reference:
///
/// ```
/// use kernel::sync::SpinLock;
///
/// struct Example {
///     a: u32,
///     b: u32,
/// }
///
/// fn example(m: &SpinLock<Example>) {
///     let mut guard = m.lock();
///     guard.a += 10;
///     guard.b += 20;
/// }
/// ```
///
/// [`spinlock_t`]: ../../../include/linux/spinlock.h
#[pin_data]
pub struct SpinLock<T: ?Sized> {
    /// The kernel `struct mutex` object.
    #[pin]
    spin_lock: Opaque<bindings::spinlock>,

    /// Spinlocks are architecture-defined. So we conservatively require them to be pinned in case
    /// some architecture or configuration (e.g., RT kernels) uses self-references now or in the
    /// future.
    #[pin]
    _pin: PhantomPinned,

    /// The data protected by the spinlock.
    data: UnsafeCell<T>,
}

// SAFETY: `SpinLock` can be transferred across thread boundaries iff the data it protects can.
unsafe impl<T: ?Sized + Send> Send for SpinLock<T> {}

// SAFETY: `SpinLock` serialises the interior mutability it provides, so it is `Sync` as long as the
// data it protects is `Send`.
unsafe impl<T: ?Sized + Send> Sync for SpinLock<T> {}

impl<T> SpinLock<T> {
    /// Constructs a new spinlock initialiser.
    #[allow(clippy::new_ret_no_self)]
    pub fn new(t: T, name: &'static CStr, key: &'static LockClassKey) -> impl PinInit<Self> {
        pin_init!(Self {
            data: UnsafeCell::new(t),
            _pin: PhantomPinned,
            // SAFETY: The first argument is always valid for writes, and `name` and `key` have
            // static lifetimes, so they are always valid.
            spin_lock <- unsafe {
                Opaque::ffi_init2(bindings::__spin_lock_init, name.as_char_ptr(), key.as_ptr())
            },
        })
    }
}

impl<T: ?Sized> SpinLock<T> {
    /// Locks the spinlock and gives the caller access to the data protected by it. Only one thread
    /// at a time is allowed to access the protected data.
    ///
    /// The interrupt state is not modified.
    #[allow(clippy::let_unit_value)]
    pub fn lock(&self) -> Guard<'_, Self> {
        let ctx = self.lock_noguard();
        // SAFETY: The spinlock was just acquired.
        unsafe { Guard::new(self, ctx) }
    }
}

// SAFETY: The underlying kernel `spinlock_t` object ensures mutual exclusion.
unsafe impl<T: ?Sized> Lock for SpinLock<T> {
    type Inner = T;
    type GuardContext = ();

    fn lock_noguard(&self) -> Self::GuardContext {
        // SAFETY: `spin_lock` points to valid memory.
        unsafe { bindings::spin_lock(self.spin_lock.get()) };
    }

    unsafe fn unlock(&self, _: &mut ()) {
        // SAFETY: The safety requirements of the function ensure that the spinlock is owned by
        // the caller.
        unsafe { bindings::spin_unlock(self.spin_lock.get()) }
    }

    fn locked_data(&self) -> &UnsafeCell<T> {
        &self.data
    }
}
