// SPDX-License-Identifier: GPL-2.0

//! RCU support.
//!
//! C header: [`include/linux/rcupdate.h`](../../../../include/linux/rcupdate.h)

use crate::{bindings, context};
use core::marker::PhantomData;

/// Evidence that the RCU read side lock is held on the current thread/CPU.
///
/// The type is explicitly not `Send` because this property is per-thread/CPU.
///
/// # Invariants
///
/// The RCU read side lock is actually held while instances of this guard exist.
pub struct Guard<'a> {
    _not_send: PhantomData<*mut ()>,
    _p: PhantomData<&'a ()>,
}

impl Guard<'_> {
    /// Acquires the RCU read side lock and returns a guard.
    pub fn new() -> Self {
        // SAFETY: An FFI call with no additional requirements.
        unsafe { bindings::rcu_read_lock() };
        // INVARIANT: The RCU read side lock was just acquired above.
        Self {
            _not_send: PhantomData,
            _p: PhantomData,
        }
    }

    /// Explicitly releases the RCU read side lock.
    pub fn unlock(self) {}
}

impl Default for Guard<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        // SAFETY: By the type invariants, the rcu read side is locked, so it is ok to unlock it.
        unsafe { bindings::rcu_read_unlock() };
    }
}

/// Acquires the RCU read side lock.
pub fn read_lock<'a>() -> Guard<'a> {
    Guard::new()
}

/// Acquires the RCU read side lock.
pub fn read_lock_with_context<'a, 'b, C: context::AsAtomic>(
    cx: &'a mut C,
) -> (&'a mut C::Atomic, Guard<'b>)
where
    'a: 'b,
{
    (cx.as_atomic(), Guard::new())
}

/// Acquires the RCU read side lock from raw-atomic context.
pub fn read_lock_from_raw_atomic<'a, 'b, C: context::RawAtomic>(
    cx: &'a mut C,
) -> (&'a mut C, Guard<'b>)
where
    'a: 'b,
{
    (cx, Guard::new())
}
