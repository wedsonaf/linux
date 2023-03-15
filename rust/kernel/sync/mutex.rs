// SPDX-License-Identifier: GPL-2.0

//! A kernel mutex.
//!
//! This module allows Rust code to use the kernel's [`struct mutex`].

use super::{Guard, Lock, LockClassKey};
use crate::{bindings, init::PinInit, pin_init, str::CStr, types::Opaque};
use core::{cell::UnsafeCell, marker::PhantomPinned};
use macros::pin_data;

/// Creates a [`Mutex`] initialiser with the given name and a newly-created lock class.
#[macro_export]
macro_rules! new_mutex {
    ($inner:expr, $name:literal) => {{
        let name = $crate::c_str!($name);
        $crate::sync::Mutex::new($inner, name, $crate::static_lock_class!())
    }};
}

/// A mutual exclusion primitive.
///
/// Exposes the kernel's [`struct mutex`]. When multiple threads attempt to lock the same mutex,
/// only one at a time is allowed to progress, the others will block (sleep) until the mutex is
/// unlocked, at which point another thread will be allowed to wake up and make progress.
///
/// Since it may block, [`Mutex`] needs to be used with care in atomic contexts.
///
/// # Examples
///
/// The following example shows how to declare, allocate and initialise a struct (`Example`) that
/// contains an inner struct (`Inner`) that is protected by a mutex.
///
/// ```
/// use kernel::{init::InPlaceInit, init::PinInit, new_mutex, pin_init, sync::Mutex};
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
///     d: Mutex<Inner>,
/// }
///
/// impl Example {
///     fn new() -> impl PinInit<Self> {
///         pin_init!(Self {
///             c: 10,
///             d <- new_mutex!(Inner { a: 20, b: 30 }, "Example::d"),
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
/// protected by a mutex despite only having a shared reference:
///
/// ```
/// use kernel::sync::Mutex;
///
/// struct Example {
///     a: u32,
///     b: u32,
/// }
///
/// fn example(m: &Mutex<Example>) {
///     let mut guard = m.lock();
///     guard.a += 10;
///     guard.b += 20;
/// }
/// ```
///
/// [`struct mutex`]: ../../../include/linux/mutex.h
#[pin_data]
pub struct Mutex<T: ?Sized> {
    /// The kernel `struct mutex` object.
    #[pin]
    mutex: Opaque<bindings::mutex>,

    /// A mutex needs to be pinned because it contains a `struct list_head` that is
    /// self-referential, so it cannot be safely moved once it is initialised.
    #[pin]
    _pin: PhantomPinned,

    /// The data protected by the mutex.
    data: UnsafeCell<T>,
}

// SAFETY: `Mutex` can be transferred across thread boundaries iff the data it protects can.
unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}

// SAFETY: `Mutex` serialises the interior mutability it provides, so it is `Sync` as long as the
// data it protects is `Send`.
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}

impl<T> Mutex<T> {
    /// Constructs a new mutex initialiser.
    #[allow(clippy::new_ret_no_self)]
    pub fn new(t: T, name: &'static CStr, key: &'static LockClassKey) -> impl PinInit<Self> {
        pin_init!(Self {
            data: UnsafeCell::new(t),
            _pin: PhantomPinned,
            // SAFETY: The first argument is always valid for writes, and `name` and `key` have
            // static lifetimes, so they are always valid.
            mutex <- unsafe {
                Opaque::ffi_init2(bindings::__mutex_init, name.as_char_ptr(), key.as_ptr())
            },
        })
    }
}

impl<T: ?Sized> Mutex<T> {
    /// Locks the mutex and gives the caller access to the data protected by it. Only one thread at
    /// a time is allowed to access the protected data.
    #[allow(clippy::let_unit_value)]
    pub fn lock(&self) -> Guard<'_, Self> {
        let ctx = self.lock_noguard();
        // SAFETY: The mutex was just acquired.
        unsafe { Guard::new(self, ctx) }
    }
}

// SAFETY: The underlying kernel `struct mutex` object ensures mutual exclusion.
unsafe impl<T: ?Sized> Lock for Mutex<T> {
    type Inner = T;
    type GuardContext = ();

    fn lock_noguard(&self) -> Self::GuardContext {
        // SAFETY: `mutex` points to valid memory.
        unsafe { bindings::mutex_lock(self.mutex.get()) };
    }

    unsafe fn unlock(&self, _: &mut ()) {
        // SAFETY: The safety requirements of the function ensure that the mutex is owned by the
        // caller.
        unsafe { bindings::mutex_unlock(self.mutex.get()) };
    }

    fn locked_data(&self) -> &UnsafeCell<T> {
        &self.data
    }
}
