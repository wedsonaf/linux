// SPDX-License-Identifier: GPL-2.0

//! A kernel read/write mutex.
//!
//! This module allows Rust code to use the kernel's [`struct rw_semaphore`].

use super::Backend;
use crate::bindings;

/// Creates an [`RwSemaphore`] initialiser with the given name and a newly-created lock class.
///
/// It uses the name if one is given, otherwise it generates one based on the file name and line
/// number.
#[macro_export]
macro_rules! new_rwsemaphore {
    ($inner:expr $(, $name:literal)? $(,)?) => {
        $crate::sync::RwSemaphore::new(
            $inner, $crate::optional_name!($($name)?), $crate::static_lock_class!())
    };
}

/// TODO: Add documentation.
pub type RwSemaphore<T> = super::Lock<T, RwSemaphoreBackend>;

/// TODO: Add documentation.
#[repr(transparent)]
pub struct RwSemaphoreBackend(bindings::rw_semaphore);

unsafe impl super::Initer for RwSemaphoreBackend {
    unsafe fn init(
        ptr: *mut Self,
        name: *const core::ffi::c_char,
        key: *mut bindings::lock_class_key,
    ) {
        // SAFETY: The safety requirements ensure that `ptr` is valid for writes, and `name` and
        // `key` are valid for read indefinitely.
        unsafe { bindings::__init_rwsem(ptr.cast(), name, key) }
    }
}

// SAFETY: The underlying kernel `struct rw_semaphore` object ensures mutual exclusion because it's
// acquired in write mode.
unsafe impl Backend for RwSemaphoreBackend {
    type GuardState = ();

    unsafe fn lock(ptr: *mut Self) -> Self::GuardState {
        // SAFETY: The safety requirements of this function ensure that `ptr` points to valid
        // memory, and that it has been initialised before.
        unsafe { bindings::down_write(ptr.cast()) };
    }

    unsafe fn unlock(ptr: *mut Self, _guard_state: &Self::GuardState) {
        // SAFETY: The safety requirements of this function ensure that `ptr` is valid and that the
        // caller is the owner of the rw semaphore.
        unsafe { bindings::up_write(ptr.cast()) };
    }
}

// SAFETY: The underlying kernel `struct rw_semaphore` object ensures that only shared references
// are accessible from other threads because it's acquired in read mode.
unsafe impl Backend<super::ReadOnly> for RwSemaphoreBackend {
    type GuardState = ();

    unsafe fn lock(ptr: *mut Self) -> Self::GuardState {
        // TODO: Add safety comment.
        unsafe { bindings::down_read(ptr.cast()) };
    }

    unsafe fn unlock(ptr: *mut Self, _guard_state: &Self::GuardState) {
        // TODO: Add safety comment.
        unsafe { bindings::up_read(ptr.cast()) };
    }
}
