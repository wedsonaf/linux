// SPDX-License-Identifier: GPL-2.0

//! Helpers to simplify the implementation of hyper-v utility services.

use crate::{
    driver, driver::DeviceRemoval, error::Result, hv, hv::vmbus, hv::vmbus::DeviceId,
    types::ForeignOwnable,
};
use alloc::boxed::Box;

/// Framework versions for util services.
pub const FW_VERSIONS: &[i32] = &[
    bindings::UTIL_FW_VERSION as _,
    bindings::UTIL_WS2K8_FW_VERSION as _,
];

const RING_SEND_SIZE: usize = 3 * super::HYP_PAGE_SIZE;
const RING_RECV_SIZE: usize = 3 * super::HYP_PAGE_SIZE;

/// A utility service.
///
/// This trait must be implemented by modules that implement an HV utility service.
pub trait Service {
    /// Type of context data associated with the service.
    type Data: ForeignOwnable + Send + Sync + 'static = ();

    /// The type holding information about each device id supported by the driver.
    type IdInfo: 'static = ();

    /// The table of device ids supported by the driver.
    const ID_TABLE: Option<driver::IdTable<'static, DeviceId, Self::IdInfo>> = None;

    /// Called when the service is bound to a device.
    fn init() -> Result<Self::Data>;

    /// Called when the service is unbound from its device.
    ///
    /// It could be beceause the device is removed from the bus or the user unbinds the driver.
    fn deinit(_data: Self::Data) {}

    /// Called before the VM is suspended.
    fn pre_suspend(_data: &mut Self::Data) -> Result {
        Ok(())
    }

    /// Called before the VM resumes.
    fn pre_resume(_data: &mut Self::Data) -> Result {
        Ok(())
    }

    /// Called when data becomes available in the bus.
    fn callback(_data: &mut Self::Data, _chan: &hv::Channel) {}
}

/// Utility driver.
pub struct Util<T: Service> {
    chan: Option<hv::ChannelCloser<T::Data>>,
    chan_data: Option<(hv::ChannelToOpen, T::Data)>,
}

impl<T: Service> hv::ChannelDataHandler for Util<T> {
    type Context = T::Data;
    fn handle_data(data: &mut Self::Context, chan: &hv::Channel) {
        T::callback(data, chan)
    }
}

impl<T: Service + 'static> vmbus::Driver for Util<T> {
    type Data = Box<Self>;
    type IdInfo = T::IdInfo;
    const ID_TABLE: Option<driver::IdTable<'static, DeviceId, Self::IdInfo>> = T::ID_TABLE;

    fn probe(
        _dev: &mut vmbus::Device,
        mut chan: hv::ChannelToOpen,
        _id_info: Option<&Self::IdInfo>,
    ) -> Result<Self::Data> {
        let svc_data = T::init()?;
        chan.set_read_mode(hv::CallMode::Direct);
        let chan = chan.open::<Self>(
            vmbus::ring_size(RING_SEND_SIZE),
            vmbus::ring_size(RING_RECV_SIZE),
            &[],
            svc_data,
        )?;
        Ok(Box::try_new(Self {
            chan: Some(chan),
            chan_data: None,
        })?)
    }

    fn remove(data: &mut Self::Data) -> Result {
        if let Some(chan) = data.chan.take() {
            // TODO: Disable callbacks, so that we can get a mutable reference before closing the
            // channel.
            let (_, svc_data) = chan.close();
            T::deinit(svc_data);
        }
        Ok(())
    }

    fn suspend(data: &mut Self::Data) -> Result {
        if let Some(chan) = data.chan.take() {
            // TODO: Disable callbacks, so that we can get a mutable reference before closing the
            // channel.
            let (to_open, mut svc_data) = chan.close();
            T::pre_suspend(&mut svc_data)?;
            data.chan_data = Some((to_open, svc_data));
        }
        Ok(())
    }

    fn resume(data: &mut Self::Data) -> Result {
        if let Some((to_open, mut svc_data)) = data.chan_data.take() {
            T::pre_resume(&mut svc_data)?;
            let chan = to_open.open::<Self>(
                vmbus::ring_size(RING_SEND_SIZE),
                vmbus::ring_size(RING_RECV_SIZE),
                &[],
                svc_data,
            )?;
            data.chan = Some(chan);
        }
        Ok(())
    }
}

impl<T: Service> DeviceRemoval for Util<T> {
    fn device_remove(&self) {}
}

/// Declares a kernel module that exposes a single vmbus utility service driver.
///
/// # Examples
///
/// ```ignore
/// # use kernel::prelude::*;
/// use kernel::hv::util;
///
/// struct MyDriver;
/// impl util::Service for MyDriver {
///     // [...]
/// #    fn init() -> Result {
/// #        Ok(())
/// #    }
/// }
///
/// kernel::module_vmbus_util_driver! {
///     type: MyDriver,
///     name: "module_name",
///     author: "Author name <author@email.com>",
///     license: "GPL",
/// }
/// ```
#[macro_export]
macro_rules! module_vmbus_util_driver {
    (type: $type:ty, $($f:tt)*) => {
        $crate::module_vmbus_driver! {
            type: $crate::hv::util::Util<$type>,
            $($f)*
        }
    };
}
