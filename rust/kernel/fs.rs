// SPDX-License-Identifier: GPL-2.0

//! Kernel file systems.
//!
//! This module allows Rust code to register new kernel file systems.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use crate::error::{code::*, from_result, to_result, Error};
use crate::types::Opaque;
use crate::{bindings, init::PinInit, str::CStr, try_pin_init, ThisModule};
use core::pin::Pin;
use macros::{pin_data, pinned_drop};

/// A file system type.
pub trait FileSystem {
    /// The name of the file system type.
    const NAME: &'static CStr;
}

/// A registration of a file system.
#[pin_data(PinnedDrop)]
pub struct Registration {
    #[pin]
    fs: Opaque<bindings::file_system_type>,
}

// SAFETY: `Registration` doesn't provide any `&self` methods, so it is safe to pass references
// to it around.
unsafe impl Sync for Registration {}

// SAFETY: Both registration and unregistration are implemented in C and safe to be performed
// from any thread, so `Registration` is `Send`.
unsafe impl Send for Registration {}

impl Registration {
    /// Creates the initialiser of a new file system registration.
    pub fn new<T: FileSystem + ?Sized>(module: &'static ThisModule) -> impl PinInit<Self, Error> {
        try_pin_init!(Self {
            fs <- Opaque::try_ffi_init(|fs_ptr: *mut bindings::file_system_type| {
                // SAFETY: `try_ffi_init` guarantees that `fs_ptr` is valid for write.
                unsafe { fs_ptr.write(bindings::file_system_type::default()) };

                // SAFETY: `try_ffi_init` guarantees that `fs_ptr` is valid for write, and it has
                // just been initialised above, so it's also valid for read.
                let fs = unsafe { &mut *fs_ptr };
                fs.owner = module.0;
                fs.name = T::NAME.as_char_ptr();
                fs.init_fs_context = Some(Self::init_fs_context_callback);
                fs.kill_sb = Some(Self::kill_sb_callback);
                fs.fs_flags = 0;

                // SAFETY: Pointers stored in `fs` are static so will live for as long as the
                // registration is active (it is undone in `drop`).
                to_result(unsafe { bindings::register_filesystem(fs_ptr) })
            }),
        })
    }

    unsafe extern "C" fn init_fs_context_callback(
        _fc_ptr: *mut bindings::fs_context,
    ) -> core::ffi::c_int {
        from_result(|| Err(ENOTSUPP))
    }

    unsafe extern "C" fn kill_sb_callback(_sb_ptr: *mut bindings::super_block) {}
}

#[pinned_drop]
impl PinnedDrop for Registration {
    fn drop(self: Pin<&mut Self>) {
        // SAFETY: If an instance of `Self` has been successfully created, a call to
        // `register_filesystem` has necessarily succeeded. So it's ok to call
        // `unregister_filesystem` on the previously registered fs.
        unsafe { bindings::unregister_filesystem(self.fs.get()) };
    }
}
