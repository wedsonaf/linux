// SPDX-License-Identifier: GPL-2.0

//! Tasks (threads and processes).
//!
//! C header: [`include/linux/sched.h`](../../../../include/linux/sched.h).

use crate::types::{ARef, ForeignOwnable, Opaque, ScopeGuard};
use crate::{bindings, c_str, error::from_err_ptr, error::Result};
use alloc::boxed::Box;
use core::{fmt, marker::PhantomData, ops::Deref, ptr};

/// Returns the currently running task.
#[macro_export]
macro_rules! current {
    () => {
        // SAFETY: Deref + addr-of below create a temporary `TaskRef` that cannot outlive the
        // caller.
        unsafe { &*$crate::task::Task::current() }
    };
}

/// Wraps the kernel's `struct task_struct`.
///
/// # Invariants
///
/// All instances are valid tasks created by the C portion of the kernel.
///
/// Instances of this type are always ref-counted, that is, a call to `get_task_struct` ensures
/// that the allocation remains valid at least until the matching call to `put_task_struct`.
///
/// # Examples
///
/// The following is an example of getting the PID of the current thread with zero additional cost
/// when compared to the C version:
///
/// ```
/// let pid = current!().pid();
/// ```
///
/// Getting the PID of the current process, also zero additional cost:
///
/// ```
/// let pid = current!().group_leader().pid();
/// ```
///
/// Getting the current task and storing it in some struct. The reference count is automatically
/// incremented when creating `State` and decremented when it is dropped:
///
/// ```
/// use kernel::{task::Task, types::ARef};
///
/// struct State {
///     creator: ARef<Task>,
///     index: u32,
/// }
///
/// impl State {
///     fn new() -> Self {
///         Self {
///             creator: current!().into(),
///             index: 0,
///         }
///     }
/// }
/// ```
#[repr(transparent)]
pub struct Task(pub(crate) Opaque<bindings::task_struct>);

// SAFETY: By design, the only way to access a `Task` is via the `current` function or via an
// `ARef<Task>` obtained through the `AlwaysRefCounted` impl. This means that the only situation in
// which a `Task` can be accessed mutably is when the refcount drops to zero and the destructor
// runs. It is safe for that to happen on any thread, so it is ok for this type to be `Send`.
unsafe impl Send for Task {}

// SAFETY: It's OK to access `Task` through shared references from other threads because we're
// either accessing properties that don't change (e.g., `pid`, `group_leader`) or that are properly
// synchronised by C code (e.g., `signal_pending`).
unsafe impl Sync for Task {}

/// The type of process identifiers (PIDs).
type Pid = bindings::pid_t;

impl Task {
    /// Returns a task reference for the currently executing task/thread.
    ///
    /// The recommended way to get the current task/thread is to use the
    /// [`current`] macro because it is safe.
    ///
    /// # Safety
    ///
    /// Callers must ensure that the returned object doesn't outlive the current task/thread.
    pub unsafe fn current() -> impl Deref<Target = Task> {
        struct TaskRef<'a> {
            task: &'a Task,
            _not_send: PhantomData<*mut ()>,
        }

        impl Deref for TaskRef<'_> {
            type Target = Task;

            fn deref(&self) -> &Self::Target {
                self.task
            }
        }

        // SAFETY: Just an FFI call with no additional safety requirements.
        let ptr = unsafe { bindings::get_current() };

        TaskRef {
            // SAFETY: If the current thread is still running, the current task is valid. Given
            // that `TaskRef` is not `Send`, we know it cannot be transferred to another thread
            // (where it could potentially outlive the caller).
            task: unsafe { &*ptr.cast() },
            _not_send: PhantomData,
        }
    }

    /// Determines if the running thread was sked to stop.
    pub fn should_stop() -> bool {
        // SAFETY: There are no extra safety requirements.
        unsafe { bindings::kthread_should_stop() }
    }

    /// Returns the group leader of the given task.
    pub fn group_leader(&self) -> &Task {
        // SAFETY: By the type invariant, we know that `self.0` is a valid task. Valid tasks always
        // have a valid group_leader.
        let ptr = unsafe { *ptr::addr_of!((*self.0.get()).group_leader) };

        // SAFETY: The lifetime of the returned task reference is tied to the lifetime of `self`,
        // and given that a task has a reference to its group leader, we know it must be valid for
        // the lifetime of the returned task reference.
        unsafe { &*ptr.cast() }
    }

    /// Returns the PID of the given task.
    pub fn pid(&self) -> Pid {
        // SAFETY: By the type invariant, we know that `self.0` is a valid task. Valid tasks always
        // have a valid pid.
        unsafe { *ptr::addr_of!((*self.0.get()).pid) }
    }

    /// Determines whether the given task has pending signals.
    pub fn signal_pending(&self) -> bool {
        // SAFETY: By the type invariant, we know that `self.0` is valid.
        unsafe { bindings::signal_pending(self.0.get()) != 0 }
    }

    /// Wakes up the task.
    pub fn wake_up(&self) {
        // SAFETY: By the type invariant, we know that `self.0.get()` is non-null and valid.
        // And `wake_up_process` is safe to be called for any valid task, even if the task is
        // running.
        unsafe { bindings::wake_up_process(self.0.get()) };
    }

    /// Starts a new kernel thread and runs it.
    ///
    /// # Examples
    ///
    /// Launches 10 threads and waits for them to complete.
    ///
    /// ```ignore
    /// use core::sync::atomic::{AtomicU32, Ordering};
    /// use kernel::sync::{CondVar, Mutex};
    /// use kernel::task::Task;
    ///
    /// kernel::init_static_sync! {
    ///     static COUNT: Mutex<u32> = 0;
    ///     static COUNT_IS_ZERO: CondVar;
    /// }
    ///
    /// fn threadfn() {
    ///     pr_info!("Running from thread {}\n", Task::current().pid());
    ///     let mut guard = COUNT.lock();
    ///     *guard -= 1;
    ///     if *guard == 0 {
    ///         COUNT_IS_ZERO.notify_all();
    ///     }
    /// }
    ///
    /// // Set count to 10 and spawn 10 threads.
    /// *COUNT.lock() = 10;
    /// for i in 0..10 {
    ///     Task::spawn(fmt!("test{i}"), threadfn).unwrap().detach();
    /// }
    ///
    /// // Wait for count to drop to zero.
    /// let mut guard = COUNT.lock();
    /// while (*guard != 0) {
    ///     COUNT_IS_ZERO.wait(&mut guard);
    /// }
    /// ```
    pub fn spawn<T: FnOnce() + Send + 'static>(name: fmt::Arguments<'_>, func: T) -> Result<KTask> {
        unsafe extern "C" fn threadfn<T: FnOnce() + Send + 'static>(
            arg: *mut core::ffi::c_void,
        ) -> core::ffi::c_int {
            // SAFETY: The thread argument is always a `Box<T>` because it is only called via the
            // thread creation below.
            let bfunc = unsafe { Box::<T>::from_foreign(arg) };
            bfunc();
            0
        }

        let arg = Box::try_new(func)?.into_foreign();

        // SAFETY: `arg` was just created with a call to `into_foreign` above.
        let guard = ScopeGuard::new(|| unsafe {
            Box::<T>::from_foreign(arg);
        });

        // SAFETY: The function pointer is always valid (as long as the module remains loaded).
        // Ownership of `raw` is transferred to the new thread (if one is actually created), so it
        // remains valid. Lastly, the C format string is a constant that require formatting as the
        // one and only extra argument.
        let ktask = from_err_ptr(unsafe {
            bindings::kthread_create_on_node(
                Some(threadfn::<T>),
                arg as _,
                bindings::NUMA_NO_NODE,
                c_str!("%pA").as_char_ptr(),
                &name as *const _ as *const core::ffi::c_void,
            )
        })?;

        // SAFETY: Since the kthread creation succeeded and we haven't run it yet, we know the task
        // is valid.
        let task = ARef::from(unsafe { &*(ktask.cast::<Task>()) });

        // Wakes up the thread, otherwise it won't run.
        task.wake_up();

        guard.dismiss();
        Ok(KTask { task: Some(task) })
    }
}

// SAFETY: The type invariants guarantee that `Task` is always ref-counted.
unsafe impl crate::types::AlwaysRefCounted for Task {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::get_task_struct(self.0.get()) };
    }

    unsafe fn dec_ref(obj: ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::put_task_struct(obj.cast().as_ptr()) }
    }
}

/// A kernel task.
///
/// It has all properties of a task, but its [`Drop`] implementation requests that the task stop
/// and waits for it to do so. When this behaviour is not desired, the caller can call
/// [`KTask::detach`] to convert a [`KTask`] to an [`ARef<Task>`].
pub struct KTask {
    task: Option<ARef<Task>>,
}

// SAFETY: `KTask` can be shared across threads for the same reason as `Task`.
unsafe impl Sync for KTask {}

impl KTask {
    /// Detaches from the kernel thread so that we don't have to wait for it to complete on `drop`.
    pub fn detach(mut self) -> ARef<Task> {
        // SAFETY: We know that `self.task` is `Some(_)` because the only way for it not to be is
        // to call this function, but it consumes `self`, so one cannot call it twice.
        unsafe { self.task.take().unwrap_unchecked() }
    }
}

impl Deref for KTask {
    type Target = Task;

    fn deref(&self) -> &Self::Target {
        // SAFETY: We know that `self.task` is `Some(_)` because the only way for it not to be is
        // to `KTask::detach`, but that consumes `KTask` so one cannot call `deref`.
        unsafe { self.task.as_ref().unwrap_unchecked() }
    }
}

impl Drop for KTask {
    fn drop(&mut self) {
        if let Some(task) = self.task.take() {
            // SAFETY: We hold a reference to the task, so it's safe to call this function.
            unsafe { bindings::kthread_stop(task.0.get()) };
        }
    }
}
