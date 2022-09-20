// SPDX-License-Identifier: GPL-2.0

//! Execution context of kernel tasks.

use core::marker::PhantomData;

/// A sleepable (non-atomic) context.
///
/// # Safety
///
/// Implementers must ensure that contexts marked as [`Sleepable`] are only constructible from
/// sleepable contexts, that is, that they reflect the actual execution context of the kernel.
pub unsafe trait Sleepable: AsAtomic + AsRawAtomic {}

/// An atomic (non-sleepable in non-RT) context.
///
/// # Safety
///
/// Implementers must ensure that contexts marked as [`Atomic`] are only constructible from atomic
/// contexts, that is, that they reflect the actual execution context of the kernel.
pub unsafe trait Atomic: AsAtomic + AsRawAtomic {}

/// A raw atomic (non-sleepable even in RT) context.
///
/// # Safety
///
/// Implementers must ensure that contexts marked as [`RawAtomic`] are only constructible from raw
/// atomic contexts, that is, that they reflect the actual execution context of the kernel.
pub unsafe trait RawAtomic: AsRawAtomic {}

/// A context that can be lowered to (or is) an atomic context.
pub trait AsAtomic {
    /// The concrete atomic type associated with this context.
    type Atomic: Atomic;

    /// Returns an atomic context from [`Self`].
    fn as_atomic(&mut self) -> &mut Self::Atomic;
}

/// A context that can be lowered to (or is) a raw atomic context.
pub trait AsRawAtomic {
    /// The concrete raw atomic type associated with this context.
    type RawAtomic: RawAtomic;

    /// Returns a raw atomic context from [`Self`].
    fn as_raw_atomic(&mut self) -> &mut Self::RawAtomic;
}

pub(crate) struct RawAtomicImpl {
    _not_send: PhantomData<*mut ()>,
}

unsafe impl RawAtomic for RawAtomicImpl {}

impl AsRawAtomic for RawAtomicImpl {
    type RawAtomic = Self;
    fn as_raw_atomic(&mut self) -> &mut Self::RawAtomic {
        self
    }
}

pub(crate) fn raw_atomic() -> RawAtomicImpl {
    RawAtomicImpl {
        _not_send: PhantomData,
    }
}

pub(crate) struct AtomicImpl {
    _not_send: PhantomData<*mut ()>,
    raw_atomic: RawAtomicImpl,
}

unsafe impl Atomic for AtomicImpl {}

impl AsAtomic for AtomicImpl {
    type Atomic = Self;
    fn as_atomic(&mut self) -> &mut Self::Atomic {
        self
    }
}

impl AsRawAtomic for AtomicImpl {
    type RawAtomic = RawAtomicImpl;
    fn as_raw_atomic(&mut self) -> &mut Self::RawAtomic {
        &mut self.raw_atomic
    }
}

pub(crate) fn atomic() -> AtomicImpl {
    AtomicImpl {
        _not_send: PhantomData,
        raw_atomic: raw_atomic(),
    }
}

pub(crate) struct SleepableImpl {
    _not_send: PhantomData<*mut ()>,
    raw_atomic: RawAtomicImpl,
    atomic: AtomicImpl,
}

unsafe impl Sleepable for SleepableImpl {}

impl AsRawAtomic for SleepableImpl {
    type RawAtomic = RawAtomicImpl;
    fn as_raw_atomic(&mut self) -> &mut Self::RawAtomic {
        &mut self.raw_atomic
    }
}

impl AsAtomic for SleepableImpl {
    type Atomic = AtomicImpl;
    fn as_atomic(&mut self) -> &mut Self::Atomic {
        &mut self.atomic
    }
}

pub(crate) fn sleepable() -> SleepableImpl {
    SleepableImpl {
        _not_send: PhantomData,
        raw_atomic: raw_atomic(),
        atomic: atomic(),
    }
}
