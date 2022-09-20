# Linux kernel execution context

Tasks in the kernel may run in a variety of different contexts. Their
ability or inability to "sleep" is an important property: in some cases,
for example, when handling a hardware interrupt, a task is not allowed to
sleep; in other contexts, for example, while servicing a system call and
not holding any spinlocks, a task is allowed to sleep. The introduction of
real-time (RT) variants of the kernel introduced additional complexity: for
example, a task may be put to sleep while holding a `spinlock_t` (but not a
`raw_spinlock_t`) in RT kernels.  More details about the kernel lock types
are their rules is available
[here](https://docs.kernel.org/locking/locktypes.html).

Kernel developers must be aware of the context in which their code is
running so that they don't violate the execution context requirements. For
example, memory allocation takes a set of flags that, among other things,
specifies whether the allocator may sleep; it is a mistake to claim we can
sleep while in atomic context.

# Problem

Violating the execution context requirements may lead to deadlocks, which
don't violate Rust safety requirements. For this reason, enforcing the
context rules has been a lower priority task.

However, we recently learned that in certain kernel configurations (e.g.,
with `CONFIG_PREEMPT=n`, which is the configuration recommended for
servers), violating these rules may result in the violation of memory
safety. In particular, RCU considers a task's attempt to sleep as a
quiescent state for that CPU, which may lead to a grace period ending
sooner, which may lead to memory being freed while still in use.

The Linux kernel community was [adamantly
against](https://lore.kernel.org/lkml/Yyr5pKpjib%2Fyqk5e@kroah.com/T/#m441736f13d57d4fac8cb0092742410178adfdf5f)
always keeping track of state that would allow the execution context to be
inferred at runtime, which would allow us to detect such RCU issues at
runtime and stop execution. So we need to explore other options on the Rust
side.

# Possible solution

One possible solution to address this issue is to carry the execution
context. The obvious drawback is that it complicates the code, but given
the extra guarantees we get, this _may_ be worth it.

Carrying contexts is not something new, for example, [Go](https://go.dev/)
uses them (it's called [Context](https://pkg.go.dev/context)) when
implementing, for example, servers so that they can keep track of things
like cancellation, timeouts, etc.

## Zero runtime cost

One major difference between our proposed solution and Go's is that ours
has zero cost at run-time. We use zero-sized structs, so they are
completely removed from the compiled code. Violations result in
compile-time errors.

## Marker traits

So the solution involves a `context` module with, among other definitions,
the following three marker traits that specify the execution context:

```rust
/// A sleepable (non-atomic) context.
pub unsafe trait Sleepable: AsAtomic + AsRawAtomic {}

/// An atomic (non-sleepable in non-RT) context.
pub unsafe trait Atomic: AsAtomic + AsRawAtomic {}

/// A raw atomic (non-sleepable even in RT) context.
pub unsafe trait RawAtomic: AsRawAtomic {}
```

## Entry points

All entry points from C code are then decorated with a context, for
example, threaded irq traits would be modified as follows (note the extra
`cx` argument):

```diff
 /// A threaded irq handler.
 pub trait ThreadedHandler {
     /// The context data associated with and made available to the handlers.
     type Data: PointerWrapper;

     /// Called from interrupt context when the irq first happens.
-    fn handle_primary_irq(_data: <Self::Data as PointerWrapper>::Borrowed<'_>) -> Return {
+    fn handle_primary_irq(
+        _cx: &mut impl context::RawAtomic,
+        _data: <Self::Data as PointerWrapper>::Borrowed<'_>,
+    ) -> Return {
         Return::WakeThread
     }

     /// Called from the handler thread.
-    fn handle_threaded_irq(data: <Self::Data as PointerWrapper>::Borrowed<'_>) -> Return;
+    fn handle_threaded_irq(
+        cx: &mut impl context::Sleepable,
+        data: <Self::Data as PointerWrapper>::Borrowed<'_>,
+    ) -> Return;
 }
```

In the `handle_primary_irq` function, a raw atomic context is provided,
while `handled_thread_irq` gets a sleepable one. The trampoline functions
that marshal the call would need to be adapted accordingly, for example
(note the call to `context::raw_atomic`):

```diff
     unsafe extern "C" fn primary_handler(
        _irq: core::ffi::c_int,
        raw_data: *mut core::ffi::c_void,
     ) -> bindings::irqreturn_t {
         // SAFETY: On registration, `into_pointer` was called, so it is safe to borrow from it here
         // because `from_pointer` is called only after the irq is unregistered.
         let data = unsafe { H::Data::borrow(raw_data) };
-        H::handle_primary_irq(data) as _
+        H::handle_primary_irq(&mut context::raw_atomic(), data) as _
     }
```

`context::sleepable`, `context::atomic`, and `context::raw_atomic` are only
available to the `kernel` crate, so they cannot be used by drivers to forge
wrong execution contexts. They will also be marked `unsafe` so entrypoints
will need to justify why their creations are acceptable.

## Functions with context requirements

These will, naturally, require an argument that specifies what the
requirements are. For example, to allocate a ref-counted object, we require
a sleepable context:

```diff
 impl<T> Ref<T> {
     /// Constructs a new reference counted instance of `T`.
-    pub fn try_new(contents: T) -> Result<Self> {
+    pub fn try_new(_cx: &mut impl context::Sleepable, contents: T) -> Result<Self> {
         let layout = Layout::new::<RefInner<T>>();
         // SAFETY: The layout size is guaranteed to be non-zero because `RefInner` contains the
         // reference count.
```

So callers will need to specify this extra argument, and this is the main
disadvantage of this approach: we need to pass this additional argument in
many parts of the code.

If we try to call this function from a non-sleepable context, we will get a
compilation error. For example:

```rust
fn ref_example(cx: &mut impl context::Atomic) -> Result<Ref<u32>> {
    Ref::try_new(cx, 0u32)
}
```

Results in the following error:

```
error[E0277]: the trait bound `impl context::Atomic: Sleepable` is not satisfied
   --> rust/kernel/sync/arc.rs:590:18
    |
590 |     Ref::try_new(cx, 0u32)
    |     ------------ ^^ the trait `Sleepable` is not implemented for `impl context::Atomic`
    |     |
    |     required by a bound introduced by this call
    |
note: required by a bound in `arc::Ref::<T>::try_new`
```

## Functions that may change context

Functions that may change context are slightly more complicated because
they need to ensure that the old context is no longer usable while the
change is in effect. To achieve his, they take the existing context as a
mutable argument and return a new one whose lifetime must be a subset of
the existing one.

This allows, for example, spinlocks to change the context from sleepable to
atomic, then return to sleepable when the lock is relesed. If the state
already atomic, it will remain atomic.

An example will hopefully make it clearer:

```rust
fn example1(cx: &mut impl context::Sleepable, a: &SpinLock<u32>) {
    let (cx1, v) = a.lock(cx);
    // `cx1` is `Atomic` and `cx` is inacessible while `cx1` is alive.
}
```

If we try to use `cx1` to acquire a mutex, for example, as below:

```rust
fn example2(cx: &mut impl context::Sleepable, a: &SpinLock<u32>, b: &Mutex<u32>) {
    let (cx1, v) = a.lock(cx);
    // `cx1` is `Atomic` and `cx` is inacessible while `cx1` is alive.
    pr_info!("{}\n", *v);
    let (cx2, w) = b.lock(cx1);
    pr_info!("{}\n", *w);
}
```

We get the following error:

```
error[E0277]: the trait bound `<impl context::Sleepable as AsAtomic>::Atomic: Sleepable` is not satisfied
   --> rust/kernel/sync/spinlock.rs:380:40
    |
380 |     let (cx2, w) = b.lock(cx1);
    |                      ---- ^^^ the trait `Sleepable` is not implemented for `<impl context::Sleepable as AsAtomic>::Atomic`
    |                      |
    |                      required by a bound introduced by this call
    |
```

If we try to drop the new context (`cx1`) without actually releasing the
spinlock and then try to use `cx` again, as in the following example:

```rust
fn example2(cx: &mut impl context::Sleepable, a: &SpinLock<u32>, b: &Mutex<u32>) {
    let (cx1, v) = a.lock(cx);
    // `cx1` is `Atomic` and `cx` is inacessible while `cx1` is alive.
    pr_info!("{}\n", *v);
    drop(cx1);
    let (cx2, w) = b.lock(cx);
    pr_info!("{}\n", *w);
}
```

We get the following error:

```
error[E0499]: cannot borrow `*cx` as mutable more than once at a time
   --> rust/kernel/sync/spinlock.rs:381:40
    |
377 |     let (cx1, v) = a.lock(cx);
    |                           -- first mutable borrow occurs here
...
381 |     let (cx2, w) = b.lock(cx);
    |                           ^^ second mutable borrow occurs here
382 |     pr_info!("{}\n", *w);
383 | }
    | - first borrow might be used here, when `v` is dropped and runs the `Drop` code for type `guard::Guard`
```

It does work if we drop the guard though:

```rust
fn example2(cx: &mut impl context::Sleepable, a: &SpinLock<u32>, b: &Mutex<u32>) {
    let (cx1, v) = a.lock(cx);
    // `cx1` is `Atomic` and `cx` is inacessible while `cx1` is alive.
    pr_info!("{}\n", *v);
    drop(v);
    let (cx2, w) = b.lock(cx);
    pr_info!("{}\n", *w);
}
```

This is the expected behaviour as we want the sleepable context to become
available again once we release the last spinlock.

## Allowing more than one context type

The contexts are strictly ordered: raw-atomic < atomic < sleepable. In
fact, we can always go from a higher context to a lower one, for example,
we can go from sleepable to atomic. We represent these relationships with
the `AsAtomic` and `AsRawAtomic` traits: if a trait implements `AsAtomic`
then it must be `>= Atomic` in the context order.

We use these traits in functions that allow more than one context, for
example, `Ref::try_new_atomic` could be declared as:

```rust
pub fn try_new_atomic(cx: &mut impl context::AsAtomic, contents: T) -> Result<Self>;
```

So that it can be called from both `Sleepable` and `Atomic` contexts, but
not `RawAtomic`.

This can also be used by functions that allow multiple contexts and change
to a specific one. For example, `RawSpinLock::lock` looks like this:

```rust
pub fn lock<'a, 'b, 'c, C: context::AsRawAtomic>(
    &'a self,
    cx: &'b mut C,
) -> (&'c mut C::RawAtomic, Guard<'a, Self, WriteLock>)
where
    'b: 'c,
    'c: 'a,
```

We note that the incoming context is any (they can all be converted to
`RawAtomic`) and the output type is `RawAtomic`.

## RCU read lock

RCU read lock doesn't fit any of the patterns above because it is allowed
to be called from any context but behaves differently depending on it.
When called from raw-atomic context, it stays in raw-atomic context;
however, when called from sleepable or atomic context, into returns in
atomic context.

The solution for this is to have two functions, one for the case where it
ends up in atomic context:

```rust
/// Acquires the RCU read side lock.
pub fn read_lock<'a, 'b, C: context::AsAtomic>(
    cx: &'a mut C,
) -> (&'a mut C::Atomic, Guard<'b>)
where
    'a: 'b,
```

And one for when it's called from raw-atomic context and stays in
raw-atomic:

```rust
/// Acquires the RCU read side lock from raw-atomic context.
pub fn read_lock_from_raw_atomic<'a, 'b, C: context::RawAtomic>(
    cx: &'a mut C,
) -> (&'a mut C, Guard<'b>)
where
    'a: 'b,
```

## Relationship with lockdep

This scheme does, at compile time, a subset of the work that lockdep does.
Namely, it prevents us from acquiring locks in disallowed contexts. For
example, lockdep detects when a task locks a `raw_spinlock_t` and then
tries to acquire a `spinlock_t`; this detection happens at runtime though,
so it requires the code to run (and lockdep to be enabled) before it can
detect the issue. Our solution prevents all such mistakes at compile time.

In the future, we may devise a way to use such contexts to carry around (at
compile time) the set of acquired locks and ensure that they're always
acquired in the correct order. We hope that having defined the context as
traits and hiding their concrete implementations will allow additional
implementations of such contexts, possibly carrying additional information,
to be implemented in the future.

## Protype

A prototype with the ideas described above is available
[here](https://github.com/wedsonaf/linux/commits/context).

It introduces variants of functions with the `with_context` suffix so that
existing code continues to work. Should we decide to adopt this solution,
those will replace their non-context-aware counterparts.

The irq handlers in `rust/kernel/irq.rs` are the most flushed out examples
of conversion to be context-aware because they have updated public traits,
C to Rust trampolines, and sample code in documentation.
