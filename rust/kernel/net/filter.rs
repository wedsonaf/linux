// SPDX-License-Identifier: GPL-2.0

//! Networking filters.
//!
//! C header: [`include/linux/netfilter.h`](../../../../../include/linux/netfilter.h)

use crate::{
    bindings, c_types,
    error::{code::*, to_result},
    net,
    types::PointerWrapper,
    ARef, AlwaysRefCounted, Result, ScopeGuard,
};
use alloc::boxed::Box;
use core::{
    marker::{PhantomData, PhantomPinned},
    pin::Pin,
};

/// Specifies the action to be taken by the netfilter core.
pub enum Disposition {
    /// The packet must be dropped.
    Drop,

    /// The packet must be accepted.
    Accept,

    /// The packet was stolen by the filter and must be treated as if it didn't exist.
    Stolen,

    /// The packet must be added to the given user-space queue.
    Queue(u16),
}

/// Hooks allowed in the [`Family::INet`], [`Family::Ipv4`], and [`Family::Ipv6`] families.
pub enum INet {
    /// Incoming packets before routing decisions are made (i.e., before it's determined if the
    /// packet is to be delivered locally or forwarded to another host).
    PreRouting = bindings::nf_inet_hooks_NF_INET_PRE_ROUTING as _,

    /// Incoming packets that are meant to be delivered locally.
    LocalIn = bindings::nf_inet_hooks_NF_INET_LOCAL_IN as _,

    /// Incoming pakcets that are meant to be forwarded to another host.
    Forward = bindings::nf_inet_hooks_NF_INET_FORWARD as _,

    /// Outgoing packet created by the local networking stack.
    LocalOut = bindings::nf_inet_hooks_NF_INET_LOCAL_OUT as _,

    /// All outgoing packets (i.e., generated locally or being forwarded to another host).
    PostRouting = bindings::nf_inet_hooks_NF_INET_POST_ROUTING as _,

    /// Equivalent to [`NetDev::Ingress`], so a device must be specified. Packets of all types (not
    /// just ipv4/ipv6 will be delivered to the filter.
    Ingress = bindings::nf_inet_hooks_NF_INET_INGRESS as _,
}

/// Hooks allowed in the [`Family::NetDev`] family.
pub enum NetDev {
    /// All packets coming in through the given device.
    Ingress = bindings::nf_dev_hooks_NF_NETDEV_INGRESS as _,

    /// All packets going out  through the given device.
    Egress = bindings::nf_dev_hooks_NF_NETDEV_EGRESS as _,
}

/// The hook families.
pub enum Family {
    ///  IPv4 and IPv6 packets.
    INet(INet),

    /// IPv4 packets.
    Ipv4(INet),

    /// All packets through a device.
    ///
    /// When this family is used, a device _must_ be specified.
    NetDev(NetDev),

    /// IPv6 packets.
    Ipv6(INet),
}

/// A network filter.
pub trait Filter {
    /// The type of the context data stored on registration and made available to the
    /// [`Filter::filter`] function.
    type Data: PointerWrapper + Sync = ();

    /// Filters the packet stored in the given buffer.
    ///
    /// It dictates to the netfilter core what the fate of the packet should be.
    fn filter(
        _data: <Self::Data as PointerWrapper>::Borrowed<'_>,
        _skb: &net::SkBuff,
    ) -> Disposition;
}

/// A registration of a networking filter.
#[derive(Default)]
pub struct Registration<T: Filter> {
    hook: bindings::nf_hook_ops,
    // A `Some(_)` namespace means the hook is registered.
    ns: Option<ARef<net::Namespace>>,
    dev: Option<ARef<net::Device>>,
    _p: PhantomData<T>,
    _pinned: PhantomPinned,
}

// SAFETY: `Registration` does not expose any of its state across threads.
unsafe impl<T: Filter> Sync for Registration<T> {}

impl<T: Filter> Registration<T> {
    /// Creates a new [`Registration`] but does not register it yet.
    ///
    /// It is allowed to move.
    pub fn new() -> Self {
        Self {
            hook: bindings::nf_hook_ops::default(),
            dev: None,
            ns: None,
            _p: PhantomData,
            _pinned: PhantomPinned,
        }
    }

    /// Creates a new filter registration and registers it.
    ///
    /// Returns a pinned heap-allocated representation of the registration.
    pub fn new_pinned(
        family: Family,
        ns: ARef<net::Namespace>,
        dev: Option<ARef<net::Device>>,
        data: T::Data,
    ) -> Result<Pin<Box<Self>>> {
        let mut filter = Pin::from(Box::try_new(Self::new())?);
        filter.as_mut().register(family, ns, dev, data)?;
        Ok(filter)
    }

    /// Registers a network filter.
    ///
    /// It must be pinned because the C portion of the kernel stores a pointer to it while it is
    /// registered.
    pub fn register(
        self: Pin<&mut Self>,
        family: Family,
        ns: ARef<net::Namespace>,
        dev: Option<ARef<net::Device>>,
        data: T::Data,
    ) -> Result {
        // SAFETY: We must ensure that we never move out of `this`.
        let this = unsafe { self.get_unchecked_mut() };
        if this.ns.is_some() {
            // Already registered.
            return Err(EINVAL);
        }

        let data_pointer = data.into_pointer();

        // SAFETY: `data_pointer` comes from the call to `data.into_pointer()` above.
        let guard = ScopeGuard::new(|| unsafe {
            T::Data::from_pointer(data_pointer);
        });

        // TODO: Get fields from a builder. (Also `net` and priority).
        match family {
            Family::INet(num) => {
                this.hook.pf = bindings::NFPROTO_INET as _;
                this.hook.hooknum = num as _;
            }
            Family::Ipv4(num) => {
                this.hook.pf = bindings::NFPROTO_IPV4 as _;
                this.hook.hooknum = num as _;
            }
            Family::Ipv6(num) => {
                this.hook.pf = bindings::NFPROTO_IPV6 as _;
                this.hook.hooknum = num as _;
            }
            Family::NetDev(num) => {
                this.hook.pf = bindings::NFPROTO_NETDEV as _;
                this.hook.hooknum = num as _;
            }
        }
        this.hook.priv_ = data_pointer as _;
        this.hook.hook = Some(Self::hook_callback);

        if let Some(ref device) = dev {
            this.hook.dev = device.0.get();
        }

        to_result(|| unsafe { bindings::nf_register_net_hook(ns.0.get(), &this.hook) })?;

        this.dev = dev;
        this.ns = Some(ns);
        guard.dismiss();
        Ok(())
    }

    unsafe extern "C" fn hook_callback(
        priv_: *mut c_types::c_void,
        skb: *mut bindings::sk_buff,
        _state: *const bindings::nf_hook_state,
    ) -> c_types::c_uint {
        let data = unsafe { T::Data::borrow(priv_) };
        match T::filter(data, unsafe { net::SkBuff::from_ptr(skb) }) {
            Disposition::Drop => bindings::NF_DROP,
            Disposition::Accept => bindings::NF_ACCEPT,
            Disposition::Queue(v) => {
                (((v as u32) << 16) & bindings::NF_VERDICT_QMASK) | bindings::NF_QUEUE
            }
            Disposition::Stolen => {
                unsafe { net::SkBuff::dec_ref(core::ptr::NonNull::new(skb).unwrap().cast()) };
                bindings::NF_STOLEN
            }
        }
    }
}

impl<T: Filter> Drop for Registration<T> {
    fn drop(&mut self) {
        if let Some(ref ns) = self.ns {
            unsafe { bindings::nf_unregister_net_hook(ns.0.get(), &self.hook) };
            unsafe { T::Data::from_pointer(self.hook.priv_) };
        }
    }
}
