// SPDX-License-Identifier: GPL-2.0

//! Kernel support for executing futures in the local thread.

use super::{Task, TaskListAdapter};
use crate::{
    bindings, c_str, c_types,
    error::{code::*, from_kernel_err_ptr, from_kernel_result},
    linked_list::{Links, List},
    sync::{CondVar, Ref, RefBorrow, SpinLock, UniqueRef},
    types::PointerWrapper,
    Result, ScopeGuard,
};
use core::task::{Context, Poll, Waker};
use core::{cell::UnsafeCell, fmt, future::Future, marker::PhantomPinned, pin::Pin};

struct WorkItem<T: 'static + Send + Future> {
    executor: Ref<Local>,
    future: UnsafeCell<T>,
    links: Links<dyn Task>,
}

unsafe impl<T: 'static + Send + Future> Sync for WorkItem<T> {}
unsafe impl<T: 'static + Send + Future> Send for WorkItem<T> {}

impl<T: 'static + Send + Future> WorkItem<T> {
    fn try_new(executor: Ref<Local>, f: T) -> Result<Ref<Self>> {
        Ref::try_new(Self {
            executor,
            future: UnsafeCell::new(f),
            links: Links::new(),
        })
    }
}

impl<T: 'static + Send + Future> super::RefWake for WorkItem<T> {
    fn wake_by_ref(self: RefBorrow<'_, Self>) {
        {
            let mut inner = self.executor.inner.lock_irqdisable();
            if inner.flags & STOP_REQUESTED != 0 {
                return;
            }

            inner.ready_list.push_back(Ref::<Self>::from(self));
        }
        self.executor.condvar.notify_one();
    }
}

impl<T: 'static + Send + Future> Task for WorkItem<T> {
    fn poll(self: Ref<Self>, cx: &mut Context<'_>) -> Poll<()> {
        // SAFETY: `future` is pinned when the work item is. The work item is pinned because it's
        // behind a `Ref`, which is always pinned.
        //
        // TODO: Talk about the UnsafeCell usage. Why is it safe?
        let future = unsafe { Pin::new_unchecked(&mut *self.future.get()) };
        future.poll(cx).map(|_| ())
    }

    fn waker(self: Ref<Self>) -> Waker {
        super::ref_waker(self)
    }

    fn get_links(&self) -> &Links<dyn Task> {
        &self.links
    }
}

/// Indicates that the executor is running.
const RUNNING: u8 = 0x1;

/// Indicates that the executor was asked to stop.
const STOP_REQUESTED: u8 = 0x2;

struct Inner {
    /// The number of futures associated with the executor.
    ///
    /// It includes both ready and not-ready futures.
    count: usize,

    /// Flags pertaining to the executor. They are defined above (e.g., [`STOP_REQUESTED`] and
    /// [`RUNNING`]).
    flags: u8,

    /// The list of futures that need to be polled.
    ready_list: List<TaskListAdapter>,
}

unsafe impl Send for Inner {}

/// An executor that runs tasks on the caller thread.
pub struct Local {
    inner: SpinLock<Inner>,
    condvar: CondVar,
    _pin: PhantomPinned,
}

impl Local {
    /// Creates a new local executor.
    pub fn try_new() -> Result<RunHandle> {
        let mut e = Pin::from(UniqueRef::try_new(Self {
            // SAFETY: `spinlock_init` is called below.
            inner: unsafe {
                SpinLock::new(Inner {
                    count: 0,
                    flags: 0,
                    ready_list: List::new(),
                })
            },
            // SAFETY: `condvar_init` is called below.
            condvar: unsafe { CondVar::new() },
            _pin: PhantomPinned,
        })?);

        // SAFETY: `inner` is pinned when the executor is.
        let inner = unsafe { e.as_mut().map_unchecked_mut(|e| &mut e.inner) };
        crate::spinlock_init!(inner, "Local::inner");

        let condvar = unsafe { e.as_mut().map_unchecked_mut(|e| &mut e.condvar) };
        crate::condvar_init!(condvar, "Local::condvar");

        Ok(RunHandle { executor: e.into() })
    }

    fn run_loop(&self, stop_on_zero_tasks: bool, interruptible: bool) -> Result {
        loop {
            let mut inner = self.inner.lock_irqdisable();
            while inner.ready_list.is_empty() && inner.flags & STOP_REQUESTED == 0 {
                if !interruptible {
                    self.condvar.wait_uninterruptible(&mut inner);
                } else if self.condvar.wait(&mut inner) {
                    return Err(EINTR);
                }
            }

            if inner.flags & STOP_REQUESTED != 0 {
                // Executor was stopped.
                break;
            }

            if let Some(work) = inner.ready_list.pop_front() {
                drop(inner);
                let waker = work.clone().waker();
                let mut ctx = Context::from_waker(&waker);

                if let Poll::Ready(_) = work.poll(&mut ctx) {
                    let mut inner = self.inner.lock_irqdisable();
                    inner.count -= 1;
                    if stop_on_zero_tasks && inner.count == 0 {
                        break;
                    }
                }
            }
        }
        Ok(())
    }

    /// Runs the executor until it is stopped.
    ///
    /// It may optionally also stop when there are no tasks (runnable or waiting) associated with
    /// it.
    fn run(&self, stop_on_zero_tasks: bool, interruptible: bool) -> Result {
        // Set the running flag only if a stop hasn't been requested yet.
        {
            let mut inner = self.inner.lock_irqdisable();

            if inner.flags & STOP_REQUESTED != 0 {
                return Ok(());
            }

            if stop_on_zero_tasks && inner.count == 0 {
                return Ok(());
            }

            inner.flags |= RUNNING;
        }

        let ret = self.run_loop(stop_on_zero_tasks, interruptible);

        // Reset the running flag.
        self.inner.lock_irqdisable().flags &= !RUNNING;
        self.condvar.notify_all();

        ret
    }

    /// Stops the executor.
    ///
    /// No new tasks can be spawned and no new ones will be polled after [`Self::stop`] is called.
    pub fn stop(&self) {
        {
            let mut inner = self.inner.lock_irqdisable();
            inner.flags |= STOP_REQUESTED;
        }
        self.condvar.notify_all();
    }

    /// Waits for the executor to stop running.
    ///
    /// It returns an [`EINTR`] if the thread wakes up due to a signal.
    pub fn join(&self) -> Result {
        let mut inner = self.inner.lock_irqdisable();
        while inner.flags & RUNNING != 0 {
            if self.condvar.wait(&mut inner) {
                return Err(EINTR);
            }
        }
        Ok(())
    }

    /// Waits for the executor to stop running.
    ///
    /// If needed, it sleeps in uninterruptible mode, so the function never fails (but also blocks
    /// even if here are pending signals).
    pub fn join_uninterruptible(&self) {
        let mut inner = self.inner.lock_irqdisable();
        while inner.flags & RUNNING != 0 {
            self.condvar.wait_uninterruptible(&mut inner);
        }
    }
}

impl super::Executor for Local {
    fn spawn(self: RefBorrow<'_, Self>, future: impl Future + 'static + Send) -> Result {
        let work = WorkItem::try_new(self.into(), future)?;
        {
            let mut inner = self.inner.lock_irqdisable();
            if inner.flags & STOP_REQUESTED != 0 {
                return Err(EPIPE);
            }

            inner.ready_list.push_back(work);
            inner.count += 1;
        }
        self.condvar.notify_one();
        Ok(())
    }
}

/// An owned permission to run the local executor.
///
/// This is so that only one thread at a time can run it.
pub struct RunHandle {
    executor: Ref<Local>,
}

impl RunHandle {
    /// Returns the executor associated with the run handle.
    ///
    /// This is so that callers can, for example, spawn new tasks.
    pub fn executor(&self) -> RefBorrow<'_, Local> {
        self.executor.as_ref_borrow()
    }

    /// Runs the executor on the caller's thread, blocking it until it runs to completion.
    pub fn run(&mut self, interruptible: bool) -> Result {
        self.executor.run(true, interruptible)
    }

    /// Runs he executor on a dedicated thread.
    ///
    /// Differently from [`RunHandle::run`], it doesn't block the caller. Instead, it creates a new
    /// thread (with the given name) and runs the executor there.
    pub fn run_on_dedicated_thread(
        self,
        thread_name: fmt::Arguments<'_>,
    ) -> Result<AutoJoinHandle> {
        let Self { executor: ex } = self;
        let raw = ex.clone().into_pointer();

        // SAFETY: `raw` was just created with a call to `into_pointer` above.
        let guard = ScopeGuard::new(|| unsafe {
            Ref::<Local>::from_pointer(raw);
        });
        let ktask = from_kernel_err_ptr(unsafe {
            bindings::kthread_create_on_node(
                Some(Self::worker),
                raw as _,
                bindings::NUMA_NO_NODE,
                c_str!("%pA").as_char_ptr(),
                &thread_name as *const _ as *const c_types::c_void,
            )
        })?;
        unsafe { bindings::wake_up_process(ktask) };
        guard.dismiss();
        Ok(AutoJoinHandle { executor: Some(ex) })
    }

    unsafe extern "C" fn worker(data: *mut c_types::c_void) -> c_types::c_int {
        from_kernel_result! {
            // SAFETY: The thread argument is always a `Ref<Local>`.
            let e = unsafe { Ref::<Local>::from_pointer(data) };
            e.run(false, false)?;
            Ok(0)
        }
    }
}

/// A handle to a local executor that automatically stops and joins (waits for it to complete) the
/// executor on drop.
pub struct AutoJoinHandle {
    executor: Option<Ref<Local>>,
}

impl AutoJoinHandle {
    /// Detaches from the auto-join handle.
    ///
    /// That is, extracts the executor from the handle and prevents it from stopping and joining
    /// the local executor.
    pub fn detach(mut self) -> Ref<Local> {
        self.executor.take().unwrap()
    }

    /// Returns the executor associated with the auto-join handle.
    ///
    /// This is so that callers can, for example, spawn new tasks.
    pub fn executor(&self) -> RefBorrow<'_, Local> {
        self.executor.as_ref().unwrap().as_ref_borrow()
    }
}

impl Drop for AutoJoinHandle {
    fn drop(&mut self) {
        if let Some(ex) = self.executor.take() {
            ex.stop();
            ex.join_uninterruptible();
        }
    }
}
