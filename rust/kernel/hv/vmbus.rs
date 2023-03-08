// SPDX-License-Identifier: GPL-2.0

//! vmbus devices and drivers.
//!
//! C header: [`include/linux/hyperv.h`](../../../../include/linux/hyperv.h)

use crate::{
    bindings, device, driver,
    error::to_result,
    error::{from_kernel_result, Result},
    str::CStr,
    types::ForeignOwnable,
    ThisModule,
};

/// A registration of a vmbus driver.
pub type Registration<T> = driver::Registration<Adapter<T>>;

/// A vmbus driver.
pub trait Driver {
    /// Data stored on device by driver.
    type Data: ForeignOwnable + Send + Sync + driver::DeviceRemoval = ();

    /// Probes for the device with the given id.
    fn probe(dev: &mut Device) -> Result<Self::Data>;

    /// Cleans any resources up that are associated with the device.
    ///
    /// This is called when the driver is detached from the device.
    fn remove(_data: &mut Self::Data) -> Result {
        Ok(())
    }

    /// Prepares the device for suspension.
    fn suspend(_data: &mut Self::Data) -> Result {
        Ok(())
    }

    /// Prepares the device to resume from suspension.
    fn resume(_data: &mut Self::Data) -> Result {
        Ok(())
    }
}

/// An adapter for the registration of vmbus drivers.
pub struct Adapter<T: Driver>(T);

impl<T: Driver> driver::DriverOps for Adapter<T> {
    type RegType = bindings::hv_driver;

    unsafe fn register(
        reg: *mut bindings::hv_driver,
        name: &'static CStr,
        module: &'static ThisModule,
    ) -> Result {
        // SAFETY: By the safety requirements of this function (defined in the trait definition),
        // `reg` is non-null and valid.
        let drv = unsafe { &mut *reg };

        drv.name = name.as_char_ptr();
        drv.probe = Some(Self::probe_callback);
        drv.remove = Some(Self::remove_callback);
        drv.suspend = Some(Self::suspend_callback);
        drv.resume = Some(Self::resume_callback);

        // SAFETY:
        //   - `drv` lives at least until the call to `vmbus_driver_unregister()` returns.
        //   - `name` pointer has static lifetime.
        //   - `module.0` lives at least as long as the module.
        //   - `probe()` and `remove()` are static functions.
        to_result(unsafe {
            bindings::__vmbus_driver_register(reg, module.0, module.name().as_char_ptr())
        })
    }

    unsafe fn unregister(reg: *mut bindings::hv_driver) {
        // SAFETY: By the safety requirements of this function (defined in the trait definition),
        // `reg` was passed (and updated) by a previous successful call to
        // `vmbus_driver_register`.
        unsafe { bindings::vmbus_driver_unregister(reg) };
    }
}

impl<T: Driver> Adapter<T> {
    extern "C" fn probe_callback(
        pdev: *mut bindings::hv_device,
        _id: *const bindings::hv_vmbus_device_id,
    ) -> core::ffi::c_int {
        from_kernel_result! {
            // SAFETY: `pdev` is valid by the contract with the C code. `dev` is alive only for the
            // duration of this call, so it is guaranteed to remain alive for the lifetime of
            // `pdev`.
            let mut dev = unsafe { Device::from_ptr(pdev) };
            let data = T::probe(&mut dev)?;
            // SAFETY: `pdev` is guaranteed to be a valid, non-null pointer.
            unsafe { bindings::hv_set_drvdata(pdev, data.into_foreign() as _) };
            Ok(0)
        }
    }

    extern "C" fn remove_callback(dev: *mut bindings::hv_device) -> core::ffi::c_int {
        from_kernel_result! {
            // SAFETY: `dev` is guaranteed to be a valid, non-null pointer.
            let ptr = unsafe { bindings::hv_get_drvdata(dev) };
            // SAFETY:
            //   - we allocated this pointer using `T::Data::into_foreign`,
            //     so it is safe to turn back into a `T::Data`.
            //   - the allocation happened in `probe`, no-one freed the memory,
            //     `remove` is the canonical kernel location to free driver data. so OK
            //     to convert the pointer back to a Rust structure here.
            let mut data = unsafe { T::Data::from_foreign(ptr) };
            let ret = T::remove(&mut data);
            <T::Data as driver::DeviceRemoval>::device_remove(&data);
            ret?;
            Ok(0)
        }
    }

    extern "C" fn suspend_callback(dev: *mut bindings::hv_device) -> core::ffi::c_int {
        from_kernel_result! {
            // SAFETY: `dev` is guaranteed to be a valid, non-null pointer.
            let ptr = unsafe { bindings::hv_get_drvdata(dev) };
            // SAFETY: `ptr` was initialised in `probe_callback` with the result of `into_foreign`,
            // and while `suspend` is being called, no other concurrent functions are called.
            let mut data = unsafe { T::Data::borrow_mut(ptr) };
            T::suspend(&mut data)?;
            Ok(0)
        }
    }

    extern "C" fn resume_callback(dev: *mut bindings::hv_device) -> core::ffi::c_int {
        from_kernel_result! {
            // SAFETY: `dev` is guaranteed to be a valid, non-null pointer.
            let ptr = unsafe { bindings::hv_get_drvdata(dev) };
            // SAFETY: `ptr` was initialised in `probe_callback` with the result of `into_foreign`,
            // and while `resume` is being called, no other concurrent functions are called.
            let mut data = unsafe { T::Data::borrow_mut(ptr) };
            T::resume(&mut data)?;
            Ok(0)
        }
    }
}

/// A vmbus device.
///
/// # Invariants
///
/// The field `ptr` is non-null and valid for the lifetime of the object.
pub struct Device {
    ptr: *mut bindings::hv_device,
}

impl Device {
    /// Creates a new device from the given pointer.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null and valid. It must remain valid for the lifetime of the returned
    /// instance.
    unsafe fn from_ptr(ptr: *mut bindings::hv_device) -> Self {
        // INVARIANT: The safety requirements of the function ensure the lifetime invariant.
        Self { ptr }
    }
}

// SAFETY: The device returned by `raw_device` is the raw vmbus device.
unsafe impl device::RawDevice for Device {
    fn raw_device(&self) -> *mut bindings::device {
        // SAFETY: By the type invariants, we know that `self.ptr` is non-null and valid.
        unsafe { &mut (*self.ptr).device }
    }
}

/// Declares a kernel module that exposes a single vmbus driver.
///
/// # Examples
///
/// ```ignore
/// # use kernel::prelude::*;
/// use kernel::hv::vmbus;
///
/// struct MyDriver;
/// impl vmbus::Driver for MyDriver {
///     // [...]
/// #    fn probe(_: &mut vmbus::Device) -> Result {
/// #        Ok(())
/// #    }
/// }
///
/// kernel::module_vmbus_driver! {
///     type: MyDriver,
///     name: "module_name",
///     author: "Author name <author@email.com>",
///     license: "GPL",
/// }
/// ```
#[macro_export]
macro_rules! module_vmbus_driver {
    ($($f:tt)*) => {
        $crate::module_driver!(<T>, $crate::hv::vmbus::Adapter<T>, { $($f)* });
    };
}
