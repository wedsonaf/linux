// SPDX-License-Identifier: GPL-2.0

//! Rust netfilter sample.

use kernel::net;
use kernel::net::filter::{self as netfilter, Disposition, Family, INet};
use kernel::prelude::*;

module! {
    type: RustNetfilter,
    name: b"rust_netfilter",
    author: b"Rust for Linux Contributors",
    description: b"Rust netfilter sample",
    license: b"GPL v2",
}

struct RustNetfilter {
    _in: Pin<Box<netfilter::Registration<Self>>>,
    _out: Pin<Box<netfilter::Registration<Self>>>,
}

impl netfilter::Filter for RustNetfilter {
    fn filter(_: (), skb: &net::SkBuff) -> Disposition {
        let data = skb.head_data();
        if let Some(h) = net::header::try_new_network(data) {
            pr_info!(
                "Packet protocol={}, len={}, src={:?}, dst={:?}\n",
                h.protocol(),
                data.len(),
                h.src_addr(),
                h.dst_addr(),
            );
        } else {
            pr_info!("Unknown packet of length={} was seen\n", data.len());
        }
        Disposition::Accept
    }
}

impl KernelModule for RustNetfilter {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        let incoming = netfilter::Registration::new_pinned(
            Family::INet(INet::PreRouting),
            net::init_ns().into(),
            None,
            (),
        )?;
        let outgoing = netfilter::Registration::new_pinned(
            Family::INet(INet::PostRouting),
            net::init_ns().into(),
            None,
            (),
        )?;
        Ok(Self {
            _in: incoming,
            _out: outgoing,
        })
    }
}
