// SPDX-License-Identifier: GPL-2.0

//! A simple spinlock implementation.
//!
//! Differently from [`super::Spinlock`], this implementation does not require pinning, so the
//! ergonomics are much improved, though the implementation is not as feature-rich as the C-based
//! one. The main advantage is that it doesn't impose unsafe blocks on callers.
//!
//! The spinlock is based on a single atomic bool, that is `true` when the lock is held and `false`
//! when the lock is available.

use super::{mutex::EmptyGuardContext, Guard, Lock, LockClassKey, LockFactory, LockIniter};
use crate::str::CStr;
use core::sync::atomic::{AtomicBool, Ordering};
use core::{cell::UnsafeCell, pin::Pin};

/// A simple spinlock.
///
/// This is mutual-exclusion primitive. It guarantees that only one CPU at a time may access the
/// data it protects. When CPUs attempt to lock the same spinlock, only one at a time is
/// allowed to progress, the others will block (spin) until the spinlock is unlocked, at which point
/// another CPU will be allowed to acquire the lock and make progress.
///
/// # Examples
///
/// ```
/// # use kernel::{Result, sync::Ref, sync::sspinlock::SpinLock};
///
/// struct Example {
///     a: u32,
///     b: u32,
/// }
///
/// static EXAMPLE: SpinLock<Example> = SpinLock::new(Example { a: 10, b: 20 });
///
/// fn inc_a(example: &SpinLock<Example>) {
///     let mut guard = example.lock();
///     guard.a += 1;
/// }
///
/// fn sum(example: &SpinLock<Example>) -> u32 {
///     let guard = example.lock();
///     guard.a + guard.b
/// }
///
/// fn try_new(a: u32, b: u32) -> Result<Ref<SpinLock<Example>>> {
///     Ref::try_new(SpinLock::new(Example { a, b }))
/// }
///
/// assert_eq!(EXAMPLE.lock().a, 10);
/// assert_eq!(sum(&EXAMPLE), 30);
///
/// inc_a(&EXAMPLE);
///
/// assert_eq!(EXAMPLE.lock().a, 11);
/// assert_eq!(sum(&EXAMPLE), 31);
///
/// # try_new(42, 43);
/// ```
pub struct SpinLock<T: ?Sized> {
    /// Determines whether the spinlock is locked.
    is_locked: AtomicBool,

    /// The data protected by the mutex.
    data: UnsafeCell<T>,
}

// SAFETY: `SpinLock` can be transferred across thread boundaries iff the data it protects can.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<T: ?Sized + Send> Send for SpinLock<T> {}

// SAFETY: `SpinLock` serialises the interior mutability it provides, so it is `Sync` as long as the
// data it protects is `Send`.
unsafe impl<T: ?Sized + Send> Sync for SpinLock<T> {}

impl<T> SpinLock<T> {
    /// Creates a new instance of the spinlock.
    pub const fn new(data: T) -> Self {
        Self {
            is_locked: AtomicBool::new(false),
            data: UnsafeCell::new(data),
        }
    }
}

impl<T: ?Sized> SpinLock<T> {
    /// Locks the mutex and gives the caller access to the data protected by it. Only one CPU at
    /// a time is allowed to access the protected data.
    pub fn lock(&self) -> Guard<'_, Self> {
        let ctx = self.lock_noguard();
        // SAFETY: The spinlock was just acquired.
        unsafe { Guard::new(self, ctx) }
    }
}

impl<T> LockFactory for SpinLock<T> {
    type LockedType<U> = SpinLock<U>;

    unsafe fn new_lock<U>(data: U) -> SpinLock<U> {
        SpinLock::new(data)
    }
}

impl<T> LockIniter for SpinLock<T> {
    fn init_lock(self: Pin<&mut Self>, _name: &'static CStr, _key: &'static LockClassKey) {}
}

// SAFETY: The spinlock implementation ensures mutual exclusion.
unsafe impl<T: ?Sized> Lock for SpinLock<T> {
    type Inner = T;
    type GuardContext = EmptyGuardContext;

    fn lock_noguard(&self) -> EmptyGuardContext {
        // SAFETY: Just an FFI call, there are no extra safety requirements.
        unsafe { bindings::preempt_disable() };
        loop {
            // Spin if the lock is currently held.
            while self.is_locked.load(Ordering::Relaxed) {
                core::hint::spin_loop();
            }

            // Try to acquire it.
            if !self.is_locked.swap(true, Ordering::Acquire) {
                return EmptyGuardContext;
            }
        }
    }

    unsafe fn unlock(&self, _: &mut EmptyGuardContext) {
        self.is_locked.store(false, Ordering::Release);

        // SAFETY: The safety requirements of this function guarantee that callers must have called
        // `lock` first, which itself has a `preempt_disable` call that this `preempt_diable` call
        // matches.
        unsafe { bindings::preempt_enable() };
    }

    fn locked_data(&self) -> &UnsafeCell<T> {
        &self.data
    }
}
