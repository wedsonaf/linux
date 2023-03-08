//! Implementation of the heartbeat utility.
use kernel::hv::{self, icmsg_hdr, util, PacketType, BUSPIPE_HDR_SIZE, ICMSG_HDR};
use kernel::prelude::*;
use kernel::{bindings, types::FromByteSlice};

const HB_MAJOR: i32 = 3;
const HB_MINOR: i32 = 0;
const HB_VERSION: i32 = HB_MAJOR << 16 | HB_MINOR;

const HB_MAJOR_1: i32 = 1;
const HB_VERSION_1: i32 = HB_MAJOR_1 << 16 | HB_MINOR;

const HB_VERSIONS: &[i32] = &[HB_VERSION, HB_VERSION_1];

const BUF_SIZE: usize = 256;

struct Heartbeat {
    version: Option<i32>,
    buf: [u8; BUF_SIZE],
}

impl util::Service for Heartbeat {
    type Data = Box<Self>;

    kernel::define_vmbus_single_id!("57164f39-9115-4e78-ab55-382f3bd5422d");

    fn init() -> Result<Self::Data> {
        Ok(Box::try_new(Self {
            version: None,
            buf: [0; BUF_SIZE],
        })?)
    }

    fn callback(data: &mut Self::Data, chan: &hv::Channel) {
        loop {
            let (requestid, recvlen) = if let Ok(ret) = chan.recv_packet(&mut data.buf) {
                ret
            } else {
                pr_err!("Heartbeat request received. Could not read into hbeat txf buf\n");
                return;
            };

            if recvlen == 0 {
                break;
            }

            let buf = &mut data.buf[..recvlen];
            let icmsghdrp = if let Some(v) = icmsg_hdr::from_bytes_mut(buf, BUSPIPE_HDR_SIZE) {
                v
            } else {
                pr_err!(
                    "Heartbeat request received. Packet length too small: {}\n",
                    recvlen
                );
                break;
            };

            icmsghdrp.icflags |=
                (bindings::ICMSGHDRFLAG_TRANSACTION | bindings::ICMSGHDRFLAG_RESPONSE) as u8;

            let msgtype = icmsghdrp.icmsgtype as u32;
            match msgtype {
                bindings::ICMSGTYPE_NEGOTIATE => {
                    let ret = hv::vmbus::prep_negotiate_resp(buf, util::FW_VERSIONS, HB_VERSIONS);
                    if let Some((_, srv_version)) = ret {
                        pr_info!(
                            "Heartbeat IC version {}.{}\n",
                            srv_version >> 16,
                            srv_version & 0xFFFF
                        );
                        data.version = Some(srv_version);
                    }
                }

                bindings::ICMSGTYPE_HEARTBEAT => {
                    // Ensure recvlen is big enough to read seq_num. Reserved area is not
                    // included in the check as the host may not fill it up entirely.
                    if let Some(seq_num) = u64::from_bytes_mut(buf, ICMSG_HDR) {
			pr_info!("Got a heartbeat message: {}\n", *seq_num);
                        *seq_num += 1;
                    } else {
                        pr_err!(
                            "Invalid heartbeat msg data. Length too small: {}\n",
                            recvlen
                        );
                    }
                }

                _ => {
                    icmsghdrp.status = bindings::HV_E_FAIL;
                    pr_err!(
                        "Heartbeat request received. Invalid msg type: {}\n",
                        msgtype
                    );
                }
            }

            let _ = chan.send_packet(buf, requestid, PacketType::DataInband);
        }
    }
}

kernel::module_vmbus_util_driver! {
    type: Heartbeat,
    name: "hv_heartbeat",
    author: "Wedson Almeida Filho <walmeida@microsoft.com>",
    license: "GPL",
}
