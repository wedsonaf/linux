// SPDX-License-Identifier: GPL-2.0

//! Synchronisation primitives.
//!
//! This module contains the kernel APIs related to synchronisation that have been ported or
//! wrapped for usage by Rust code in the kernel and is shared by all of them.
//!
//! # Example
//!
//! ```no_run
//! # use kernel::prelude::*;
//! # use kernel::mutex_init;
//! # use kernel::sync::Mutex;
//! # use alloc::boxed::Box;
//! # use core::pin::Pin;
//! // SAFETY: `init` is called below.
//! let mut data = Pin::from(Box::new(unsafe { Mutex::new(0) }));
//! mutex_init!(data.as_mut(), "test::data");
//! *data.lock() = 10;
//! pr_info!("{}\n", *data.lock());
//! ```

use crate::str::CStr;
use crate::{bindings, c_types};
use core::pin::Pin;

mod arc;
mod condvar;
mod guard;
mod locked_by;
mod mutex;
mod spinlock;

pub use arc::{Ref, RefBorrow};
pub use condvar::CondVar;
pub use guard::{Guard, Lock};
pub use locked_by::LockedBy;
pub use mutex::Mutex;
pub use spinlock::SpinLock;

extern "C" {
    fn rust_helper_signal_pending() -> c_types::c_int;
    fn rust_helper_cond_resched() -> c_types::c_int;
}

/// Safely initialises an object that has an `init` function that takes a name and a lock class as
/// arguments, examples of these are [`Mutex`] and [`SpinLock`]. Each of them also provides a more
/// specialised name that uses this macro.
#[doc(hidden)]
#[macro_export]
macro_rules! init_with_lockdep {
    ($obj:expr, $name:expr) => {{
        static mut CLASS: core::mem::MaybeUninit<$crate::bindings::lock_class_key> =
            core::mem::MaybeUninit::uninit();
        let obj = $obj;
        let name = $crate::c_str!($name);
        // SAFETY: `CLASS` is never used by Rust code directly; the kernel may change it though.
        #[allow(unused_unsafe)]
        unsafe {
            $crate::sync::NeedsLockClass::init(obj, name, CLASS.as_mut_ptr())
        };
    }};
}

/// A trait for types that need a lock class during initialisation.
///
/// Implementers of this trait benefit from the [`init_with_lockdep`] macro that generates a new
/// class for each initialisation call site.
pub trait NeedsLockClass {
    /// Initialises the type instance so that it can be safely used.
    ///
    /// Callers are encouraged to use the [`init_with_lockdep`] macro as it automatically creates a
    /// new lock class on each usage.
    ///
    /// # Safety
    ///
    /// `key` must point to a valid memory location as it will be used by the kernel.
    unsafe fn init(self: Pin<&mut Self>, name: &'static CStr, key: *mut bindings::lock_class_key);
}

/// Determines if a signal is pending on the current process.
pub fn signal_pending() -> bool {
    // SAFETY: No arguments, just checks `current` for pending signals.
    unsafe { rust_helper_signal_pending() != 0 }
}

/// Reschedules the caller's task if needed.
pub fn cond_resched() -> bool {
    // SAFETY: No arguments, reschedules `current` if needed.
    unsafe { rust_helper_cond_resched() != 0 }
}

#[doc(hidden)]
#[macro_export]
macro_rules! expand_init_call {
    ($tname:ty, $arg:ident, $name:ident, mutex) => {{
        let inner = unsafe { $arg.as_mut().map_unchecked_mut(|a| &mut a.$name) };
        $crate::mutex_init!(inner, core::concat!(stringify!($tname), "::", stringify!($name)));
    }};
    ($tname:ty, $arg:ident, $name:ident, spinlock) => {{
        let inner = unsafe { $arg.as_mut().map_unchecked_mut(|a| &mut a.$name) };
        $crate::spinlock_init!!(inner, core::concat!(stringify!($tname), "::", stringify!($name)));
    }};
    ($tname:ty, $arg:ident, $name:ident, condvar) => {{
        let inner = unsafe { $arg.as_mut().map_unchecked_mut(|a| &mut a.$name) };
        $crate::condvar_init!(inner, core::concat!(stringify!($tname), "::", stringify!($name)));
    }};
    ($tname:ty, $arg:ident, $name:ident) => {};
}

#[doc(hidden)]
#[macro_export]
macro_rules! expand_initer {
    ($e:expr, mutex) => {{ let arg = $e; unsafe { $crate::sync::Mutex::new(arg) } }};
    ($e:expr, spinlock) => {{ let arg = $e; unsafe { $crate::sync::SpinLock::new(arg) } }};
    ($e:expr, condvar) => {{ unsafe { $crate::sync::CondVar::new() } }};
    ($e:expr) => { $e };
}

#[macro_export]
macro_rules! new_ref {
    ($tname:ty { $($([$prim:ident])? $name:ident : $e:expr,)* }) => {{
        type X = $tname;
        $crate::sync::Ref::try_new_and_init(
            X { $($name : {$crate::expand_initer!($e $(, $prim)?)},)* },
            |mut arg| { $($crate::expand_init_call!($tname, arg, $name $(, $prim)?);)*})
    }}
}
