// SPDX-License-Identifier: GPL-2.0

//! A kernel rw semaphore where acccess to contents can be revoked at runtime.

use crate::{
    bindings,
    str::CStr,
    sync::{Guard, NeedsLockClass, RwSemaphore},
};
use core::{
    mem::ManuallyDrop,
    ops::{Deref, DerefMut},
    pin::Pin,
};

/// The state within a `RevocableRwSemaphore` that is protected by an rw semaphore.
///
/// We don't use simply `Option<T>` because we need to drop in-place because the contents are
/// implicitly pinned.
struct Inner<T: ?Sized> {
    is_available: bool,
    data: ManuallyDrop<T>,
}

/// A rw semaphore whose contents can become inaccessible at runtime.
///
/// Once access is revoked and all concurrent users complete (i.e., all existing instances of
/// [`RevocableRwSemaphoreGuard`] are dropped), the wrapped object is also dropped.
///
/// TODO: Update example
/// # Examples
///
/// ```
/// # use kernel::sync::RevocableMutex;
/// # use kernel::revocable_mutex_init;
/// # use core::pin::Pin;
///
/// struct Example {
///     a: u32,
///     b: u32,
/// }
///
/// fn add_two(v: &RevocableMutex<Example>) -> Option<u32> {
///     let guard = v.try_lock()?;
///     Some(guard.a + guard.b)
/// }
///
/// fn example() {
///     // SAFETY: We call `revocable_mutex_init` immediately below.
///     let mut v = unsafe { RevocableMutex::new(Example { a: 10, b: 20 }) };
///     // SAFETY: We never move out of `v`.
///     let pinned = unsafe { Pin::new_unchecked(&mut v) };
///     revocable_mutex_init!(pinned, "example::v");
///     assert_eq!(add_two(&v), Some(30));
///     v.revoke();
///     assert_eq!(add_two(&v), None);
/// }
/// ```
pub struct RevocableRwSemaphore<T: ?Sized> {
    inner: RwSemaphore<Inner<T>>,
}

/// Safely initialises a [`RevocableRwSemaphore`] with the given name, generating a new lock class.
#[macro_export]
macro_rules! revocable_rwsemaphore_init {
    ($rwsem:expr, $name:literal) => {
        $crate::init_with_lockdep!($rwsem, $name)
    };
}

impl<T> RevocableRwSemaphore<T> {
    /// Creates a new revocable instance of the given data.
    ///
    /// # Safety
    ///
    /// The caller must call [`RevocableRwSemaphore::init`] before using the revocable rw semaphore.
    pub unsafe fn new(data: T) -> Self {
        Self {
            // SAFETY: The safety requirements of this function require that
            // `RevocableRawSemaphore::init` be called before the returned object can be used.
            // Rw semaphore initialisation is called from `RevocableRwSemaphore::init`, so we
            // satisfy the requirement from `RwSemaphore`.
            inner: unsafe {
                RwSemaphore::new(Inner {
                    is_available: true,
                    data: ManuallyDrop::new(data),
                })
            },
        }
    }
}

impl<T> NeedsLockClass for RevocableRwSemaphore<T> {
    unsafe fn init(
        self: Pin<&mut Self>,
        name: &'static CStr,
        key1: *mut bindings::lock_class_key,
        key2: *mut bindings::lock_class_key,
    ) {
        // SAFETY: `inner` is pinned when `self` is.
        let rwsem = unsafe { self.map_unchecked_mut(|r| &mut r.inner) };

        // SAFETY: The safety requirements of this function satisfy the ones for `RwSemaphore::init`
        // (they're the same).
        unsafe { rwsem.init(name, key1, key2) };
    }
}

impl<T: ?Sized> RevocableRwSemaphore<T> {
    /// Tries to lock (and access) the \[revocable\] wrapped object.
    ///
    /// Returns `None` if the object has been revoked and is therefore no longer accessible.
    ///
    /// Returns a guard that gives access to the object otherwise; the object is guaranteed to
    /// remain accessible while the guard is alive. Callers are allowed to sleep while holding on
    /// to the returned guard.
    pub fn try_lock(&self) -> Option<RevocableRwSemaphoreGuard<'_, T>> {
        let inner = self.inner.write();
        if !inner.is_available {
            return None;
        }
        Some(RevocableRwSemaphoreGuard::new(inner))
    }

    /// Revokes access to and drops the wrapped object.
    ///
    /// Revocation and dropping happens after ongoing accessors complete.
    pub fn revoke(&self) {
        let mut inner = self.inner.write();
        if !inner.is_available {
            // Already revoked.
            return;
        }

        inner.is_available = false;

        // SAFETY: We know `inner.data` is valid because `is_available` was true. We'll drop it
        // here, and given that we set `is_available` to false above, it won't be dropped again.
        unsafe { ManuallyDrop::drop(&mut inner.data) };
    }
}

impl<T: ?Sized> Drop for RevocableRwSemaphore<T> {
    fn drop(&mut self) {
        self.revoke();
    }
}

// TODO: Unify guards.
/// A guard that allows access to a revocable object and keeps it alive.
pub struct RevocableRwSemaphoreGuard<'a, T: ?Sized> {
    guard: Guard<'a, RwSemaphore<Inner<T>>>,
}

impl<'a, T: ?Sized> RevocableRwSemaphoreGuard<'a, T> {
    fn new(guard: Guard<'a, RwSemaphore<Inner<T>>>) -> Self {
        Self { guard }
    }

    /// Returns a pinned mutable reference to the wrapped object.
    pub fn as_pinned_mut(&mut self) -> Pin<&mut T> {
        // SAFETY: Revocable rw semaphores must be pinned, so we choose to always project the data
        // as pinned as well (i.e., we guarantee we never move it).
        unsafe { Pin::new_unchecked(&mut self.guard.data) }
    }
}

impl<T: ?Sized> Deref for RevocableRwSemaphoreGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.guard.data
    }
}

impl<T: ?Sized> DerefMut for RevocableRwSemaphoreGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.guard.data
    }
}
