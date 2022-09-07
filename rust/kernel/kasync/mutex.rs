// SPDX-License-Identifier: GPL-2.0

//! A async mutex implementation.

use crate::{
    sync::sspinlock::SpinLock,
    unsafe_list::{Adapter, Links, List},
};
use core::{
    cell::UnsafeCell,
    future::Future,
    pin::Pin,
    sync::atomic::{AtomicU8, Ordering},
    task::{Context, Poll, Waker},
};

/// The value that is OR'd into [`Mutex::value`] when the mutex is locked.
const LOCKED: u8 = 1;

/// The value that is OR'd into [`Mutex::value`] when the mutex has a waiter.
const WAITER: u8 = 2;

/// A simple mutex.
///
/// This is mutual-exclusion primitive. It guarantees that only one task at a time may access the
/// data it protects. When multiple tasks attempt to lock the same mutex, only one at a time is
/// allowed to progress, the others will block (sleep, giving up the executor) until the mutex is
/// unlocked, at which point another task will be allowed to wake up and make progress.
///
/// # Examples
///
/// TODO: Write examples.
/// ```
/// # use kernel::{Result, sync::Ref, sync::smutex::Mutex};
///
/// struct Example {
///     a: u32,
///     b: u32,
/// }
///
/// static EXAMPLE: Mutex<Example> = Mutex::new(Example { a: 10, b: 20 });
///
/// fn inc_a(example: &Mutex<Example>) {
///     let mut guard = example.lock();
///     guard.a += 1;
/// }
///
/// fn sum(example: &Mutex<Example>) -> u32 {
///     let guard = example.lock();
///     guard.a + guard.b
/// }
///
/// fn try_new(a: u32, b: u32) -> Result<Ref<Mutex<Example>>> {
///     Ref::try_new(Mutex::new(Example { a, b }))
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
pub struct Mutex<T: ?Sized> {
    /// Contains flags indicating the state of the lock: [`LOCKED`] and [`WAITER`].
    value: AtomicU8,

    /// A list with all waiters.
    waiter_list: SpinLock<List<Waiter>>,

    /// The data protected by the mutex.
    data: UnsafeCell<T>,
}

// SAFETY: `Mutex` can be transferred across thread boundaries iff the data it protects can.
#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}

// SAFETY: `Mutex` serialises the interior mutability it provides, so it is `Sync` as long as the
// data it protects is `Send`.
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}

impl<T> Mutex<T> {
    /// Creates a new instance of the mutex.
    pub const fn new(data: T) -> Self {
        Self {
            value: AtomicU8::new(0),
            waiter_list: SpinLock::new(List::new()),
            data: UnsafeCell::new(data),
        }
    }
}

impl<T: ?Sized> Mutex<T> {
    /// Locks the mutex and gives the caller access to the data protected by it. Only one task at
    /// a time is allowed to access the protected data.
    pub fn lock(&self) -> impl Future<Output = Guard<'_, T>> {
        MutexFuture::new(self)
    }

    pub fn try_lock(&self) -> Option<Guard<'_, T>> {
        if self.value.load(Ordering::Relaxed) & LOCKED == 0
            && self.value.fetch_or(LOCKED, Ordering::Acquire) & LOCKED == 0
        {
            Some(Guard { mutex: self })
        } else {
            None
        }
    }
}

pub struct Guard<'a, T: ?Sized> {
    mutex: &'a Mutex<T>,
}

impl<T: ?Sized> core::ops::Deref for Guard<'_, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // TODO: Annotate.
        unsafe { &*self.mutex.data.get() }
    }
}

impl<T: ?Sized> core::ops::DerefMut for Guard<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // TODO: Annotate.
        unsafe { &mut *self.mutex.data.get() }
    }
}

impl<T: ?Sized> Drop for Guard<'_, T> {
    fn drop(&mut self) {
        let v = self.mutex.value.fetch_and(!LOCKED, Ordering::Release);
        if v & WAITER != 0 {
            let list = self.mutex.waiter_list.lock();
            if let Some(head) = list.front() {
                // TODO: Add safety annotation.
                if let Some(waker) = unsafe { &head.as_ref().waker } {
                    waker.wake_by_ref();
                }
            }
        }
    }
}

struct Waiter {
    waker: Option<Waker>,
    links: Links<Waiter>,
}

// SAFETY: This adapter is the only one that uses `Waiter::links`.
unsafe impl Adapter for Waiter {
    type EntryType = Self;
    fn to_links(obj: &Self) -> &Links<Self> {
        &obj.links
    }
}

struct MutexFuture<'a, T: ?Sized> {
    mutex: &'a Mutex<T>,
    is_first: bool,
    waiter: Waiter,
}

impl<'a, T: ?Sized> MutexFuture<'a, T> {
    fn new(mutex: &'a Mutex<T>) -> Self {
        Self {
            mutex,
            is_first: true,
            waiter: Waiter {
                waker: None,
                links: Links::new(),
            },
        }
    }
}

impl<T: ?Sized> Drop for MutexFuture<'_, T> {
    fn drop(&mut self) {
        // TODO: Remove from list if registered.
    }
}

impl<'a, T: ?Sized> Future for MutexFuture<'a, T> {
    type Output = Guard<'a, T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: We never move out of `this`.
        let mut this = unsafe { self.get_unchecked_mut() };

        if this.is_first {
            if let Some(g) = this.mutex.try_lock() {
                return Poll::Ready(g);
            }

            this.is_first = false;
            this.waiter.waker = Some(cx.waker().clone());

            // SAFETY: The object was just initialised, so it's not in any lists yet, it remains
            // alive until we remove it, and it is pinned so cannot move.
            unsafe { this.mutex.waiter_list.lock().push_back(&this.waiter) };

            let old = this
                .mutex
                .value
                .fetch_or(WAITER | LOCKED, Ordering::Acquire);
            if old & LOCKED == 0 {
                // We managed to acquire the mutex before sleeping. We have set the `WAITER` bit as
                // well, which will make the unlock path try to wake waiters, but that's ok.
                // TODO: Add safety annotation.
                unsafe { this.mutex.waiter_list.lock().remove(&this.waiter) };
                return Poll::Ready(Guard { mutex: this.mutex });
            }
        } else if let Some(g) = this.mutex.try_lock() {
            let mut list = this.mutex.waiter_list.lock();
            // TODO: Add safety annotation.
            unsafe { list.remove(&this.waiter) };
            if list.is_empty() {
                this.mutex.value.fetch_and(!WAITER, Ordering::Relaxed);
            }
            return Poll::Ready(g);
        }

        Poll::Pending
    }
}
