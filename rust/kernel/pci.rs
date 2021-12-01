// SPDX-License-Identifier: GPL-2.0

// TODO: Document.
//! PCI.

use crate::{
    bindings, bit, device, driver, error::code::*, error::from_kernel_result, io_mem::Resource,
    irq, str::CStr, sync::Ref, types::PointerWrapper, Error, Result,
};
use alloc::vec::Vec;
use core::{fmt, ops::Deref, pin::Pin};

/// TODO: Document.
pub trait Driver: Sync + Sized {
    /// Data stored on device by driver.
    type InnerData: driver::DeviceRemoval + 'static;

    type Data: PointerWrapper + Deref<Target = Self::InnerData> = Ref<Self::InnerData>;

    type IdInfo: 'static = ();
    const ID_TABLE: &'static [(u32, u32, Option<Self::IdInfo>)];

    /// Probes for the device with the given resources and id.
    fn probe(dev: &mut Device, id: &(u32, u32, Option<Self::IdInfo>)) -> Result<Self::Data>;

    fn remove(_data: &Self::Data) {}
}

#[macro_export]
macro_rules! declare_pci_id_entry {
    (($first:expr, $second:expr)) => {
        ($first, $second, None)
    };
    (($first:expr, $second:expr, $third:expr)) => {
        ($first, $second, Some($third))
    };
}

#[macro_export]
macro_rules! declare_pci_id_table {
    ($(($($entry:tt)*),)*) => {
        const ID_TABLE: &'static [(u32, u32, Option<Self::IdInfo>)] = &[
            $($crate::declare_pci_id_entry!(($($entry)*)),)*
        ];
    };

    // Conver case without a trailing comma.
    ($(($($entry:tt)*)),*) => {
        $crate::declare_pci_id_table!{ $(($($entry)*),)*}
    }
}

unsafe extern "C" fn probe_callback<T: Driver>(
    pdev: *mut bindings::pci_dev,
    id: *const bindings::pci_device_id,
) -> core::ffi::c_int {
    from_kernel_result! {
        let mut dev = Device::from_ptr(pdev);
        let index = unsafe { (*id).driver_data } as usize;
        if index >= T::ID_TABLE.len() {
            return Err(ENXIO);
        }
        let data = T::probe(&mut dev, &T::ID_TABLE[index])?;
        let ptr = T::Data::into_pointer(data);
        unsafe { bindings::pci_set_drvdata(pdev, ptr as _) };
        Ok(0)
    }
}

unsafe extern "C" fn remove_callback<T: Driver>(dev: *mut bindings::pci_dev) {
    let ptr = unsafe { bindings::pci_get_drvdata(dev) };
    let data = unsafe { T::Data::from_pointer(ptr) };
    T::remove(&data);
    <T::InnerData as driver::DeviceRemoval>::device_remove(&data);
}

pub struct Registration {
    registered: bool,
    pci_driver: bindings::pci_driver,
    table: Vec<bindings::pci_device_id>,
}

impl Registration {
    pub fn new() -> Self {
        Self {
            registered: false,
            pci_driver: bindings::pci_driver::default(),
            table: Vec::new(),
        }
    }

    pub fn register<T: Driver>(self: Pin<&mut Self>, name: &'static CStr) -> Result {
        // SAFETY: We never move out of `this`.
        let this = unsafe { self.get_unchecked_mut() };
        if this.registered {
            // Already registered.
            return Err(EINVAL);
        }

        if this.table.is_empty() {
            this.build_table::<T>()?;
        }

        this.pci_driver.name = name.as_char_ptr();
        this.pci_driver.id_table = &this.table[0];
        this.pci_driver.probe = Some(probe_callback::<T>);
        this.pci_driver.remove = Some(remove_callback::<T>);
        let ret = unsafe {
            bindings::__pci_register_driver(
                &mut this.pci_driver,
                // TODO: Use THIS_MODULE.
                core::ptr::null_mut(),
                name.as_char_ptr(),
            )
        };
        if ret < 0 {
            return Err(Error::from_kernel_errno(ret));
        }
        this.registered = true;
        Ok(())
    }

    pub fn build_table<T: Driver>(&mut self) -> Result {
        // TODO: This is not ideal because the table is built at runtime. OK for now, but once Rust
        // fully supports const generics, we can build the table at compile time.
        self.table.try_reserve_exact(T::ID_TABLE.len() + 1)?;
        for (i, (class, mask, _)) in T::ID_TABLE.iter().enumerate() {
            self.table.try_push(bindings::pci_device_id {
                vendor: bindings::PCI_ANY_ID as _,
                device: bindings::PCI_ANY_ID as _,
                subvendor: bindings::PCI_ANY_ID as _,
                subdevice: bindings::PCI_ANY_ID as _,
                class: *class,
                class_mask: *mask,
                driver_data: i as _,
                override_only: 0, // TODO: Check this is ok.
            })?;
        }
        self.table.try_push(bindings::pci_device_id::default())?;
        Ok(())
    }
}

impl Default for Registration {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Registration {
    fn drop(&mut self) {
        if self.registered {
            unsafe { bindings::pci_unregister_driver(&mut self.pci_driver) };
        }
    }
}

unsafe impl Sync for Registration {}
unsafe impl Send for Registration {}

pub struct Device {
    // TODO: Make this private.
    pub ptr: *mut bindings::pci_dev,
    res_taken: u64,
}

impl Device {
    fn from_ptr(ptr: *mut bindings::pci_dev) -> Self {
        Self { ptr, res_taken: 0 }
    }

    pub fn enable_device_mem(&self) -> Result {
        let ret = unsafe { bindings::pci_enable_device_mem(self.ptr) };
        if ret != 0 {
            Err(Error::from_kernel_errno(ret))
        } else {
            Ok(())
        }
    }

    pub fn set_master(&self) {
        unsafe { bindings::pci_set_master(self.ptr) };
    }

    pub fn select_bars(&self, flags: core::ffi::c_ulong) -> i32 {
        unsafe { bindings::pci_select_bars(self.ptr, flags) }
    }

    pub fn request_selected_regions(&self, bars: i32, name: &'static CStr) -> Result {
        let ret =
            unsafe { bindings::pci_request_selected_regions(self.ptr, bars, name.as_char_ptr()) };
        if ret != 0 {
            Err(Error::from_kernel_errno(ret))
        } else {
            Ok(())
        }
    }

    pub fn take_resource(&mut self, index: usize) -> Option<Resource> {
        let pdev = unsafe { &*self.ptr };

        // Fail if the index is beyond the end or if it has already been taken.
        if index >= pdev.resource.len() || self.res_taken & bit(index) != 0 {
            return None;
        }

        self.res_taken |= bit(index);
        Resource::new(pdev.resource[index].start, pdev.resource[index].end)
    }

    pub fn irq(&self) -> Option<u32> {
        let pdev = unsafe { &*self.ptr };

        if pdev.irq == 0 {
            None
        } else {
            Some(pdev.irq)
        }
    }

    pub fn alloc_irq_vectors(&mut self, min_vecs: u32, max_vecs: u32, flags: u32) -> Result<u32> {
        let ret = unsafe {
            bindings::pci_alloc_irq_vectors_affinity(
                self.ptr,
                min_vecs,
                max_vecs,
                flags,
                core::ptr::null_mut(),
            )
        };
        if ret < 0 {
            Err(Error::from_kernel_errno(ret))
        } else {
            Ok(ret as _)
        }
    }

    pub fn alloc_irq_vectors_affinity(
        &mut self,
        min_vecs: u32,
        max_vecs: u32,
        pre: u32,
        post: u32,
        flags: u32,
    ) -> Result<u32> {
        let mut affd = bindings::irq_affinity {
            pre_vectors: pre,
            post_vectors: post,
            ..bindings::irq_affinity::default()
        };

        let ret = unsafe {
            bindings::pci_alloc_irq_vectors_affinity(
                self.ptr,
                min_vecs,
                max_vecs,
                flags | bindings::PCI_IRQ_AFFINITY,
                &mut affd,
            )
        };
        if ret < 0 {
            Err(Error::from_kernel_errno(ret))
        } else {
            Ok(ret as _)
        }
    }

    pub fn free_irq_vectors(&mut self) {
        unsafe { bindings::pci_free_irq_vectors(self.ptr) };
    }

    pub fn request_irq<T: irq::Handler>(
        &self,
        index: u32,
        data: T::Data,
        name_args: fmt::Arguments<'_>,
    ) -> Result<irq::Registration<T>> {
        let ret = unsafe { bindings::pci_irq_vector(self.ptr, index) };
        if ret < 0 {
            return Err(Error::from_kernel_errno(ret));
        }

        irq::Registration::try_new(ret as _, data, irq::flags::SHARED, name_args)
    }
}

unsafe impl device::RawDevice for Device {
    fn raw_device(&self) -> *mut bindings::device {
        unsafe { &mut (*self.ptr).dev }
    }
}
