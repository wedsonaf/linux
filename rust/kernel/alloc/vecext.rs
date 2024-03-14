// SPDX-License-Identifier: GPL-2.0

//! Extensions to [`Vec`] for fallible allocations.

use alloc::{collections::TryReserveError, vec::Vec};
use core::result::Result;

/// Extensions to [`Vec`].
pub trait VecExt<T>: Sized {
    /// Creates a new [`Vec`] instance with at least the given capacity.
    fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError>;

    /// Appends an element to the back of the [`Vec`] instance.
    fn try_push(&mut self, v: T) -> Result<(), TryReserveError>;

    /// Pushes clones of the elements of slice into the [`Vec`] instance.
    fn try_extend_from_slice(&mut self, other: &[T]) -> Result<(), TryReserveError>
    where
        T: Clone;
}

impl<T> VecExt<T> for Vec<T> {
    fn try_with_capacity(capacity: usize) -> Result<Self, TryReserveError> {
        let mut v = Vec::new();
        v.try_reserve(capacity)?;
        Ok(v)
    }

    fn try_push(&mut self, v: T) -> Result<(), TryReserveError> {
        if let Err(retry) = self.push_within_capacity(v) {
            self.try_reserve(1)?;
            let _ = self.push_within_capacity(retry);
        }
        Ok(())
    }

    fn try_extend_from_slice(&mut self, other: &[T]) -> Result<(), TryReserveError>
    where
        T: Clone,
    {
        let extra_cap = self.capacity() - self.len();
        if extra_cap > 0 {
            self.try_reserve(extra_cap)?;
        }

        for item in other {
            self.try_push(item.clone())?;
        }

        Ok(())
    }
}
