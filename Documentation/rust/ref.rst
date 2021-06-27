``Ref<T>``
==========

This document describes some of the design choices we made around the
implementation of the ``Ref<T>`` type.

Why?
----

First we'll tackle why we wrote it instead of reusing, for example, the standard
library's ``Arc<T>`` type, which already offers an abstraction for
reference-counted allocations.

There are several reasons:

- The main reason has to do with the behaviour when the number of references
  *overflows*. This usually occurs when there is a code path that leaks
  references (Rust makes it harder for this to happen but not impossible, as
  leaking is not considered a violation of memory safety); without additional
  protections, a use-after-free attack may be possible if the attacker is able
  to increment the count until it wraps around to 0; then a legitimate codepath
  that increments the count then decrements it will see 0 and free the memory.
  Other legitimate code that had a reference to the object [rightfully] expects
  the memory to still be allocated so it may touch freed memory. ``Arc<T>``
  prevents this by *aborting* execution.

  The kernel, in contrast, issues a warning and saturates the reference count.
  This is preserves memory safety as any legitimate users are allowed to
  continue to use the allocated memory. The drawback is that the memory is
  leaked forever (so susceptible to DoS), but the advantage is that execution
  continues.

  We want Rust kernel code to behave as similarly as C code (as long as it's
  safe), so we chose to reuse the kernel's ``refcount_t`` C implementation.
  ``Ref<T>`` is a Rust abstraction that uses ``refcount_t``.

- Weak references: ``Arc<T>`` supports weak references, which is a great feature
  to have, but the vast majority of kernel code does not use it. It requires the
  maintenance of two counts, so it doubles the size requirement as compared to
  ``refcount_t`` (in fact, since ``refcount_t`` uses a 32-bit count,
  the memory requirement quadruples on 64-bit architectures from 4 to 16 bytes).
  By not having this feature in ``Ref<T>``, we make it a zero-cost abstraction
  when compared to C's ``refcount_t``.

- Pinning: ``Arc<T>`` provides a ``get_mut()`` method that allows users to
  optionally (when the reference count is 1) get a mutable reference to the
  underlying memory (as an ``&mut T``). This means that ``Arc<T>`` isn't
  inherently pinned, as the underlying object may be moved through
  ``get_mut()``. Given that the kernel has many self-referential (e.g., mutexes)
  data structures, an inherently pinned data structure is preferred, so
  ``Ref<T>`` does not provide any way to get a mutable reference to the
  underlying object. During construction, a ``RefUnique<T>`` instance can be
  used to initialise state, then it is converted to ``Ref<T>`` which is
  inherently pinned and only allows interior mutability.

- Zero-cost leaking/recovery:
- Borrowing: when ``Ref<T>`` objects are stored in C code (e.g., as the
  ``private_data`` field in ``struct file``), we'd use ``Arc<T>::into_raw``,
  which returns a ``*const T`` so we are able to use the wrapped object, but we
  are not able to increment the reference count because we don't have a way
  safe way to access the refcount to increment it.

- Borrowing a ref-counted object and being able to increment the refcount.
- Code reuse: by reusing existing code, we avoid duplication of subtle code
  (e.g., barriers between decrement and freeing) and benefit from any future
  improvements to the C implementation.

Disadvantages:

- At the moment, we need several unstable features to implement ``Ref<T>``,
  including internal ones that are tightly integrated with the compiler.
- ``Ref<T>`` is not fully compatible with ``Arc<T>``, so seasoned Rust
  developers won't be able to leverage familiarity of ``Arc<T>`` when writing
  Linux kernel code, although many of the concepts are very similar, so should
  carry over.
