// SPDX-License-Identifier: GPL-2.0

//! Headers of networking packets.

use crate::be;

pub fn try_new_network(buf: &[u8]) -> Option<&dyn Network> {
    // The version will determine if it's IPv4 or IPv6.
    match buf[0] >> 4 {
        4 => Some(IPv4::try_from_slice(buf)?),
        6 => Some(IPv6::try_from_slice(buf)?),
        _ => None
    }
}

pub trait Network {
    fn src_addr(&self) -> &[u8];
    fn dst_addr(&self) -> &[u8];
    fn protocol(&self) -> u32;
}

#[repr(C)]
pub struct IPv4 {
    pub version_ihl: u8,
    pub dscp_ecn: u8,
    pub total_len: be<u16>,
    pub id: be<u16>,
    pub flags_frag_offset: be<u16>,
    pub ttl: u8,
    pub protocol: u8,
    pub xsum: be<u16>,
    pub src_addr: [u8; 4],
    pub dst_addr: [u8; 4],
}

impl IPv4 {
    const MIN_LEN: usize = core::mem::size_of::<Self>();

    /// Instantiates an IPv4 packet header if validation succeeds.
    pub fn try_from_slice(buf: &[u8]) -> Option<&Self> {
        if buf.len() < Self::MIN_LEN {
            return None;
        }
        let ipv4 = unsafe { &*buf.as_ptr().cast::<Self>() };
        if ipv4.version() != 4 {
            return None;
        }
        let header_len = ipv4.header_len().into();
        if header_len < Self::MIN_LEN || buf.len() < header_len {
            return None;
        }
        Some(ipv4)
    }

    pub fn version(&self) -> u8 {
        self.version_ihl >> 4
    }

    pub fn header_len(&self) -> u8 {
        (self.version_ihl & 0xf) << 2
    }
}

impl Network for IPv4 {
    fn src_addr(&self) -> &[u8] {
        &self.src_addr
    }

    fn dst_addr(&self) -> &[u8] {
        &self.dst_addr
    }

    fn protocol(&self) -> u32 {
        self.protocol as _
    }
}

#[repr(C)]
pub struct IPv6 {
    pub version_tc_flow_label: be<u32>,
    pub payload_len: be<u16>,
    pub next_header: u8,
    pub hop_limit: u8,
    pub src_addr: [u8; 16],
    pub dst_addr: [u8; 16],
}

impl IPv6 {
    const MIN_LEN: usize = core::mem::size_of::<Self>();

    /// Instantiates an IPv6 packet header if validation succeeds.
    pub fn try_from_slice(buf: &[u8]) -> Option<&Self> {
        if buf.len() < Self::MIN_LEN {
            return None;
        }
        let ipv6 = unsafe { &*buf.as_ptr().cast::<Self>() };
        crate::pr_info!("Version is {} {}\n", ipv6.version(), buf[0] >> 4);
        if ipv6.version() != 6 {
            return None;
        }
        Some(ipv6)
    }

    pub fn version(&self) -> u8 {
        (self.version_tc_flow_label.to_ne() >> 28) as _
    }
}

impl Network for IPv6 {
    fn src_addr(&self) -> &[u8] {
        &self.src_addr
    }

    fn dst_addr(&self) -> &[u8] {
        &self.dst_addr
    }

    fn protocol(&self) -> u32 {
        self.next_header as _
    }
}
