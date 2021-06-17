// SPDX-License-Identifier: GPL-2.0

//! Devicetree and Open Firmware abstractions.
//!
//! C header: [`include/linux/of_*.h`](../../../../include/linux/of_*.h)

use alloc::boxed::Box;

use crate::{
    bindings, c_types,
    error::{Error, Result},
    str::CStr,
    types::PointerWrapper,
};

use core::mem::transmute;

type InnerTable = Box<[bindings::of_device_id; 2]>;

/// Wraps a kernel Open Firmware / devicetree match table.
///
/// Rust drivers may create this structure to match against devices
/// described in the devicetree.
///
/// The ['PointerWrapper'] trait provides conversion to/from a raw pointer,
/// suitable to be assigned to a `bindings::device_driver::of_match_table`.
///
/// # Invariants
///
/// The final array element is always filled with zeros (the default).
pub struct OfMatchTable(InnerTable);

impl OfMatchTable {
    /// Creates a [`OfMatchTable`] from a single `compatible` string.
    pub fn new(compatible: &'static CStr) -> Result<Self> {
        let tbl = Box::try_new([
            Self::new_of_device_id(compatible)?,
            bindings::of_device_id::default(),
        ])?;
        // INVARIANTS: we allocated an array with `default()` as its final
        // element, therefore that final element will be filled with zeros,
        // and the invariant above will hold.
        Ok(Self(tbl))
    }

    fn new_of_device_id(compatible: &'static CStr) -> Result<bindings::of_device_id> {
        let mut buf = [0_u8; 128];
        if compatible.len() > buf.len() {
            return Err(Error::EINVAL);
        }
        buf.get_mut(..compatible.len())
            .ok_or(Error::EINVAL)?
            .copy_from_slice(compatible.as_bytes());
        Ok(bindings::of_device_id {
            // SAFETY: re-interpretation from [u8] to [c_types::c_char] of same length is always safe.
            compatible: unsafe { transmute::<[u8; 128], [c_types::c_char; 128]>(buf) },
            ..Default::default()
        })
    }
}

impl PointerWrapper for OfMatchTable {
    type Borrowed = <InnerTable as PointerWrapper>::Borrowed;

    fn into_pointer(self) -> *const c_types::c_void {
        // Per the invariant above, the generated pointer points to an
        // array of `bindings::of_device_id`, where the final element is
        // filled with zeros (the sentinel). Therefore, it's suitable to
        // be assigned to `bindings::device_driver::of_match_table`.
        self.0.into_pointer()
    }

    unsafe fn borrow(ptr: *const c_types::c_void) -> Self::Borrowed {
        // SAFETY: The safety  requirements for this function are the same as the ones for
        // `InnerTable::borrow`.
        unsafe { InnerTable::borrow(ptr) }
    }

    unsafe fn from_pointer(p: *const c_types::c_void) -> Self {
        // SAFETY: The passed pointer comes from a previous call to [`InnerTable::into_pointer()`].
        Self(unsafe { InnerTable::from_pointer(p) })
    }
}
