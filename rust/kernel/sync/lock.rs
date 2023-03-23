// SPDX-License-Identifier: GPL-2.0

//! Generic kernel lock.
//!
//! It contains generic Rust declarations that allow for different backends (e.g., mutexes,
//! spinlocks, raw spinlock) to be provided.

use super::LockClassKey;
use crate::{bindings, init, init::PinInit, pin_init, str::CStr, types::Opaque};
use core::{cell::UnsafeCell, marker::PhantomData, marker::PhantomPinned};
use macros::pin_data;

/// Creates a [`Lock`] initialiser with the given name and a newly-created lock class.
#[macro_export]
macro_rules! new_lock {
    ($inner:expr, $name:literal) => {{
        let name = $crate::c_str!($name);
        $crate::sync::lock::Lock::new($inner, name, $crate::static_lock_class!())
    }};
}

/// A mutual exclusion primitive.
///
/// Exposes one of the kernel locking primitives. Which one is exposed depends on the lock banckend
/// specified as the generic parameter `T`.
///
/// // TODO: Update examples below.
/// # Examples
#[pin_data]
pub struct Lock<T: ?Sized, B: LockBackend> {
    /// The kernel `struct mutex` object.
    #[pin]
    state: Opaque<B::State>,

    /// A mutex needs to be pinned because it contains a `struct list_head` that is
    /// self-referential, so it cannot be safely moved once it is initialised.
    #[pin]
    _pin: PhantomPinned,

    /// The data protected by the mutex.
    data: UnsafeCell<T>,
}

/// The "backend" of a lock.
///
/// It is the actual implementation of the lock, without the need to repeat patterns used in all
/// locks.
pub trait LockBackend {
    /// The state required by the lock.
    type State;

    /// The state required to be kept between lock and unlock.
    type GuardState;

    /// Initialises the lock.
    ///
    /// # Safety
    ///
    /// `ptr` must be valid for write for the duration of the call, while `name` and `key` must
    /// remain valid for read indefinitely.
    unsafe fn init(
        ptr: *mut Self::State,
        name: *const core::ffi::c_char,
        key: *mut bindings::lock_class_key,
    );

    /// Acquires the lock, making the caller its owner.
    ///
    /// # Safety
    ///
    /// Callers must ensure that `Lock::init` has been previously called.
    #[must_use]
    unsafe fn lock(ptr: *mut Self::State) -> Self::GuardState;

    /// Releases the lock, giving up its ownership.
    ///
    /// # Safety
    ///
    /// It must only be called by the current owner of the lock.
    unsafe fn unlock(ptr: *mut Self::State, state: Self::GuardState);
}

// SAFETY: `Lock` can be transferred across thread boundaries iff the data it protects can.
unsafe impl<T: ?Sized + Send, B: LockBackend> Send for Lock<T, B> {}

// SAFETY: `Lock` serialises the interior mutability it provides, so it is `Sync` as long as the
// data it protects is `Send`.
unsafe impl<T: ?Sized + Send, B: LockBackend> Sync for Lock<T, B> {}

impl<T, B: LockBackend> Lock<T, B> {
    /// Constructs a new lock initialiser.
    #[allow(clippy::new_ret_no_self)]
    pub fn new(t: T, name: &'static CStr, key: &'static LockClassKey) -> impl PinInit<Self> {
        pin_init!(Self {
            data: UnsafeCell::new(t),
            _pin: PhantomPinned,
            state <- unsafe { init::pin_init_from_closure(move |slot| {
                B::init(Opaque::raw_get(slot), name.as_char_ptr(), key.as_ptr());
                Ok(())
            }) },
        })
    }
}

impl<T: ?Sized, B: LockBackend> Lock<T, B> {
    /// Locks the mutex and gives the caller access to the data protected by it. Only one thread at
    /// a time is allowed to access the protected data.
    #[allow(clippy::let_unit_value)]
    pub fn lock(&self) -> Guard<'_, T, B> {
        // SAFETY: The constructor of the type calls `init`, so the existence of the object proves
        // that `init` was called.
        let state = unsafe { B::lock(self.state.get()) };
        // SAFETY: The lock was just acquired.
        unsafe { Guard::new(self, state) }
    }
}

/// A lock guard.
///
/// Allows mutual exclusion primitives that implement the [`LockBackend`] trait to automatically
/// unlock when a guard goes out of scope. It also provides a safe and convenient way to access the
/// data protected by the lock.
#[must_use = "the lock unlocks immediately when the guard is unused"]
pub struct Guard<'a, T: ?Sized, B: LockBackend> {
    pub(crate) lock: &'a Lock<T, B>,
    pub(crate) state: Option<B::GuardState>,
    _not_send: PhantomData<*mut ()>,
}

// SAFETY: `Guard` is sync when the data protected by the lock is also sync.
unsafe impl<T: Sync + ?Sized, B: LockBackend> Sync for Guard<'_, T, B> {}

impl<T: ?Sized, B: LockBackend> core::ops::Deref for Guard<'_, T, B> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // SAFETY: The caller owns the lock, so it is safe to deref the protected data.
        unsafe { &*self.lock.data.get() }
    }
}

impl<T: ?Sized, B: LockBackend> core::ops::DerefMut for Guard<'_, T, B> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY: The caller owns the lock, so it is safe to deref the protected data.
        unsafe { &mut *self.lock.data.get() }
    }
}

impl<T: ?Sized, B: LockBackend> Drop for Guard<'_, T, B> {
    fn drop(&mut self) {
        // SAFETY: The caller owns the lock, so it is safe to unlock it.
        unsafe { B::unlock(self.lock.state.get(), self.state.take().unwrap()) };
    }
}

impl<'a, T: ?Sized, B: LockBackend> Guard<'a, T, B> {
    /// Constructs a new immutable lock guard.
    ///
    /// # Safety
    ///
    /// The caller must ensure that it owns the lock.
    pub(crate) unsafe fn new(lock: &'a Lock<T, B>, state: B::GuardState) -> Self {
        Self {
            lock,
            state: Some(state),
            _not_send: PhantomData,
        }
    }
}
