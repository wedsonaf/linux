// SPDX-License-Identifier: GPL-2.0

//! Kernel async functionality.

use crate::{bindings, sync::NoWaitLock};
use core::task::{Context, Poll, Waker};
use core::{cell::UnsafeCell, future::Future, marker::PhantomPinned, pin::Pin, time};

pub mod executor;
#[cfg(CONFIG_NET)]
pub mod net;

pub fn sleep(duration: time::Duration) -> impl Future<Output = ()> {
    #[derive(PartialEq)]
    enum State {
        Initial,
        TimerStarted,
    }

    struct Sleeper {
        state: State,
        expire_time: bindings::ktime_t,
        timer: UnsafeCell<bindings::hrtimer>,
        waker: NoWaitLock<Option<Waker>>,
        _pin: PhantomPinned,
    }

    unsafe impl Send for Sleeper {}

    impl Sleeper {
        fn new(duration: time::Duration) -> Self {
            let ns = i64::try_from(duration.as_nanos()).unwrap_or(i64::MAX);
            Self {
                // TODO: Use `ktime_add`.
                expire_time: unsafe { bindings::ktime_get() }.saturating_add(ns),
                timer: UnsafeCell::new(bindings::hrtimer::default()),
                state: State::Initial,
                waker: NoWaitLock::new(None),
                _pin: PhantomPinned,
            }
        }

        unsafe extern "C" fn timer_callback(
            arg: *mut bindings::hrtimer,
        ) -> bindings::hrtimer_restart {
            let s = unsafe { &*crate::container_of!(arg, Sleeper, timer) };
            if let Some(mut guard) = s.waker.try_lock() {
                if let Some(w) = guard.take() {
                    drop(guard);
                    w.wake();
                }
            }
            bindings::hrtimer_restart_HRTIMER_NORESTART
        }
    }

    impl Drop for Sleeper {
        fn drop(&mut self) {
            if self.state == State::TimerStarted {
                unsafe { bindings::hrtimer_cancel(self.timer.get()) };
            }
        }
    }

    impl Future for Sleeper {
        type Output = ();

        // TODO: Consider that the task may wake up due to another reason. For example, a `select`
        // where another branch caused the wake up.
        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
            // Check if the timer has already expired.
            if unsafe { bindings::ktime_compare(bindings::ktime_get(), self.expire_time) } >= 0 {
                return Poll::Ready(());
            }

            // Store away the latest waker.
            if let Some(mut guard) = self.waker.try_lock() {
                let old = core::mem::replace(&mut *guard, Some(cx.waker().clone()));
                drop(guard);
                drop(old);
            } else {
                cx.waker().wake_by_ref();
            }

            match self.state {
                State::TimerStarted => Poll::Pending,
                State::Initial => {
                    // SAFETY: We never move out of `this`.
                    let this = unsafe { self.get_unchecked_mut() };

                    this.state = State::TimerStarted;

                    unsafe {
                        bindings::hrtimer_init(
                            this.timer.get(),
                            bindings::CLOCK_MONOTONIC as _,
                            bindings::hrtimer_mode_HRTIMER_MODE_ABS,
                        )
                    };
                    this.timer.get_mut().function = Some(Self::timer_callback);
                    unsafe {
                        bindings::hrtimer_start_range_ns(
                            this.timer.get(),
                            this.expire_time,
                            0,
                            bindings::hrtimer_mode_HRTIMER_MODE_ABS,
                        )
                    };
                    Poll::Pending
                }
            }
        }
    }

    Sleeper::new(duration)
}
