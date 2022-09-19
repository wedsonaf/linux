// SPDX-License-Identifier: GPL-2.0

//! RCU support.
//!
//! C header: [`include/linux/rcupdate.h`](../../../../include/linux/rcupdate.h)

use crate::{bindings, PointerWrapper};
use core::{
    ffi::{c_ulong, c_void},
    marker::PhantomData,
    sync::atomic::{AtomicPtr, Ordering},
};

/// Evidence that the RCU read side lock is held on the current thread/CPU.
///
/// The type is explicitly not `Send` because this property is per-thread/CPU.
///
/// # Invariants
///
/// The RCU read side lock is actually held while instances of this guard exist.
pub struct Guard {
    _not_send: PhantomData<*mut ()>,
}

impl Guard {
    /// Acquires the RCU read side lock and returns a guard.
    pub fn new() -> Self {
        // SAFETY: An FFI call with no additional requirements.
        unsafe { bindings::rcu_read_lock() };
        // INVARIANT: The RCU read side lock was just acquired above.
        Self {
            _not_send: PhantomData,
        }
    }

    /// Explicitly releases the RCU read side lock.
    pub fn unlock(self) {}
}

impl Default for Guard {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        // SAFETY: By the type invariants, the rcu read side is locked, so it is ok to unlock it.
        unsafe { bindings::rcu_read_unlock() };
    }
}

/// Acquires the RCU read side lock.
pub fn read_lock() -> Guard {
    Guard::new()
}

/// Waits for a grace period to complete before continuing.
pub fn synchronize() {
    // TODO: Add safety annotation.
    unsafe { bindings::synchronize_rcu() };
}

/// An rcu-protected pointer.
///
/// Users are allowed to fetch
///
/// # Examples
///
/// ```
/// use alloc::boxed::Box;
/// use kernel::sync::rcu::{self, Rcu};
///
/// let guard = rcu::read_lock();
///
/// let rv1 = Rcu::new(Box::try_new(0u32).unwrap());
/// let bv = Box::try_new(1u32).unwrap();
///
/// let x = rv1.get(&guard);
/// let to_free = rv1.replace(bv);
/// pr_info!("Value: {}\n", *x);
/// drop(guard);
/// ```
#[repr(transparent)]
pub struct Rcu<T: PointerWrapper> {
    ptr: AtomicPtr<c_void>,
    _p: PhantomData<T>,
}

impl<T: PointerWrapper> Rcu<T> {
    /// Creates a new instance of an rcu-protected pointer.
    pub fn new(data: T) -> Self {
        Self {
            ptr: AtomicPtr::new(data.into_pointer() as _),
            _p: PhantomData,
        }
    }
}

impl<T: PointerWrapper> Rcu<T> {
    /// Gets (borrows) the value pointed-to by the rcu-protected pointer.
    ///
    /// The value is guaranteed to remain valid as long as the rcu guard is alive, even if `self`
    /// is dropped.
    pub fn get<'a>(&self, _guard: &'a Guard) -> T::Borrowed<'a> {
        // We don't need an acquire barrier here because because there is an address dependency on
        // accesses through the returned reference.
        //
        // TODO: Indicate pairing.
        let ptr = self.ptr.load(Ordering::Acquire);
        // TODO: Add safety annotation.
        unsafe { T::borrow(ptr) }
    }

    /// Replaces the current pointer with a new one.
    ///
    /// The previous pointer may remain in use until a grace period expires, so it is returned in a
    /// [`ToFree`] wrapper, which ensures that it is not freed too early.
    pub fn replace(&self, new: T) -> ToFree<T> {
        let new_ptr = new.into_pointer() as _;
        let old_ptr = self.ptr.swap(new_ptr, Ordering::Release);

        // SAFETY: By the type invariants, we know that `old_ptr` was returned by a previous call
        // to `T::into_pointer`. We also know that it isn't visible by other threads because we
        // replaced it with `new_ptr` above.
        unsafe { ToFree::new(old_ptr) }
    }

    /// Replaces the pointer with null.
    ///
    /// This is meant to be used when optimising the drop implementation of a struct that has
    /// multiple rcu-protected fields: one would call `prepare_drop` on all of them, synchronise,
    /// then free them all. This is more efficient than synchronising (i.e., waiting for a grace
    /// period) on each one.
    ///
    /// # Safety
    ///
    /// This breaks an invariant, so it must only be called right before `drop` is called.
    pub unsafe fn prepare_drop(&mut self) -> ToFree<T> {
        let old_ptr = self.ptr.swap(core::ptr::null_mut(), Ordering::Release);
        // TODO: Add annotation.
        unsafe { ToFree::new(old_ptr) }
    }
}

impl<T: PointerWrapper> Drop for Rcu<T> {
    fn drop(&mut self) {
        let ptr = *self.ptr.get_mut();
        if !ptr.is_null() {
            // If the pointer is non-null, we wait for a grace period and then free it. If it's
            // null, `prepare_drop` was called and the pointer will be freed by the caller.
            synchronize();

            // TODO: Add safety annotation.
            unsafe { T::from_pointer(ptr) };
        }
    }
}

/// An rcu-protected pointer that needs to be freed.
///
/// Its drop implementation will ensure that a grace-period has expired since the pointer was last
/// visible. This can be done by waiting for one within the drop implementation itself or realising
/// that one has already completed via its polled cookie.
///
/// # Examples
///
/// The following example waits for a single grace period to free both instances:
///
/// ```
/// use kernel::{PointerWrapper, sync::rcu};
///
/// fn free_example<T: PointerWrapper>(a: rcu::ToFree<T>, b: rcu::ToFree<T>) {
///     rcu::synchronize();
///     drop(a);
///     drop(b);
/// }
/// ```
pub struct ToFree<T: PointerWrapper> {
    ptr: *mut c_void,
    rcu_cookie: c_ulong,
    _p: PhantomData<T>,
}

impl<T: PointerWrapper> ToFree<T> {
    /// Creates a new rcu-protected pointer that needs to be freed.
    ///
    /// # Safety
    ///
    /// `ptr` must come from a previous call to `T::into_pointer` with no matching call to
    /// `T::from_pointer` having been called yet. Additionally, the pointer must have already been
    /// removed from its `Rcu` holder, that is, it must not be visible anymore.
    unsafe fn new(ptr: *mut c_void) -> Self {
        Self {
            ptr,
            // SAFETY: The safety requirements of this function, in particular the one about the
            // visibility of the pointer, satisfy the safety requirements for the call below.
            rcu_cookie: unsafe { bindings::get_state_synchronize_rcu() },
            _p: PhantomData,
        }
    }
}

impl<T: PointerWrapper> Drop for ToFree<T> {
    fn drop(&mut self) {
        // TODO: Add safety annotation.
        unsafe { bindings::cond_synchronize_rcu(self.rcu_cookie) };
        // TODO: Add safety annotation.
        unsafe { T::from_pointer(self.ptr) };
    }
}
