// SPDX-License-Identifier: GPL-2.0

//! Driver for NVMe devices.
//!
//! Based on the C driver written by Matthew Wilcox <willy@linux.intel.com>.

use alloc::boxed::Box;
use core::{
    cell::UnsafeCell,
    convert::TryInto,
    format_args,
    mem::ManuallyDrop,
    pin::Pin,
    sync::atomic::{fence, AtomicU16, AtomicU32, AtomicU64, Ordering},
};
use kernel::{
    bindings,
    blk::mq,
    c_str, declare_pci_id_table,
    device::{self, Device, RawDevice},
    dma,
    error::code::*,
    io_mem::IoMem,
    irq, pci,
    prelude::*,
    sync::{Ref, RefBorrow, SpinLock, UniqueRef},
    AtomicOptionalBoxedPtr, ScopeGuard,
};

#[allow(dead_code)]
mod nvme_defs;

use nvme_defs::*;

struct NvmeQueues {
    admin: Option<Ref<NvmeQueue>>,
    io: Vec<Ref<NvmeQueue>>,
}

struct NvmeShadow {
    dbs: dma::CoherentAllocation<u32, dma::CoherentAllocator>,
    eis: dma::CoherentAllocation<u32, dma::CoherentAllocator>,
}

struct NvmeData {
    db_stride: usize,
    dev: Device,
    instance: u32,
    shadow: Option<NvmeShadow>,
    queues: SpinLock<NvmeQueues>,
    dma_pool: Ref<dma::Pool<le<u64>>>,
}

struct NvmeResources {
    bar: IoMem<8192>,
}

type DeviceData = device::Data<(), NvmeResources, NvmeData>;

struct NvmeRequest {
    dma_pool: Ref<dma::Pool<le<u64>>>,
    dma_addr: AtomicU64,
    result: AtomicU32,
    status: AtomicU16,
    direction: AtomicU32,
    len: AtomicU32,
    dev: Device,
    cmd: UnsafeCell<NvmeCommand>,
    sg_count: AtomicU32,
    page_count: AtomicU32,
    first_dma: AtomicU64,
    mapping_data: AtomicOptionalBoxedPtr<MappingData>,
}

struct NvmeNamespace {
    id: u32,
    lba_shift: u32,
}

const NVME_MAX_KB_SZ: usize = 4096;
const NVME_MAX_SEGS: usize = 127;
const NVME_CTRL_PAGE_SIZE: usize = kernel::PAGE_SIZE;

const fn div_round_up(a: usize, b: usize) -> usize {
    (a + (b - 1)) / b
}

const fn npages_prp() -> usize {
    let nprps = div_round_up(
        NVME_MAX_KB_SZ * 1024 + NVME_CTRL_PAGE_SIZE,
        NVME_CTRL_PAGE_SIZE,
    );
    div_round_up(8 * nprps, NVME_CTRL_PAGE_SIZE - 8)
}

struct MappingData {
    sg: [bindings::scatterlist; NVME_MAX_SEGS],
    pages: [usize; npages_prp()],
}

impl Default for MappingData {
    fn default() -> Self {
        Self {
            sg: [bindings::scatterlist::default(); NVME_MAX_SEGS],
            pages: [0; npages_prp()],
        }
    }
}

fn calculate_max_blocks(cap: u64, mdts: u8) -> Option<u32> {
    if mdts == 0 {
        return None;
    }

    let mps_min = ((cap >> 48) & 0xf) as u32;
    let ps_in_blocks = 1u32.checked_shl(mps_min.checked_add(3)?)?;
    ps_in_blocks.checked_mul(1u32.checked_shl(mdts.into())?)
}

struct NvmeDevice;

impl NvmeDevice {
    fn alloc_ns(
        max_sectors: u32,
        instance: u32,
        nsid: u32,
        id: &NvmeIdNs,
        tagset: Ref<mq::TagSet<Self>>,
        rt: &NvmeLbaRangeType,
    ) -> Result<mq::GenDisk<Self>> {
        if rt.attributes & NVME_LBART_ATTRIB_HIDE != 0 {
            return Err(ENODEV);
        }

        let lbaf = (id.flbas & 0xf) as usize;
        let lba_shift = id.lbaf[lbaf].ds as u32;
        let ns = Box::try_new(NvmeNamespace {
            id: nsid,
            lba_shift,
        })?;
        let disk = mq::GenDisk::try_new(tagset, ns)?;
        disk.set_name(format_args!("nvme{}n{}", instance, nsid))?;
        disk.set_capacity(id.nsze.into() << (lba_shift - bindings::SECTOR_SHIFT));
        disk.set_queue_logical_block_size(1 << lba_shift);
        disk.set_queue_max_hw_sectors(max_sectors);
        disk.set_queue_max_segments(NVME_MAX_SEGS as _);
        disk.set_queue_virt_boundary(NVME_CTRL_PAGE_SIZE - 1);
        Ok(disk)
    }

    fn set_queue_count(count: u32, mq: &mq::RequestQueue<Self>) -> Result<u32> {
        let q_count = (count - 1) | ((count - 1) << 16);
        let res = nvme_set_features(mq, NVME_FEAT_NUM_QUEUES, q_count, 0)?;
        Ok(core::cmp::min(res & 0xffff, res >> 16) + 1)
    }

    fn setup_io_queues(
        dev: &Ref<DeviceData>,
        pci_dev: &mut pci::Device,
        admin_queue: &Ref<NvmeQueue>,
        mq: &mq::RequestQueue<NvmeDevice>,
    ) -> Result<Ref<mq::TagSet<Self>>> {
        let mut nr_io_queues = kernel::num_possible_cpus();
        let result = Self::set_queue_count(nr_io_queues, mq)?;
        if result < nr_io_queues {
            nr_io_queues = result;
        }

        admin_queue.unregister_irq();
        // TODO: Check what happens when free_irq_vectors is called before all irqs are
        // unregistered.
        pci_dev.free_irq_vectors();
        // TODO: Check what happens if alloc_irq_vectors_affinity is called before
        // free_irq_vectors.
        let irqs = pci_dev.alloc_irq_vectors_affinity(
            1,
            nr_io_queues + 1,
            1,
            0,
            bindings::PCI_IRQ_ALL_TYPES,
        )?;
        admin_queue.register_irq(pci_dev)?;

        let tagset = mq::TagSet::try_new(nr_io_queues, dev.clone())?;

        // TODO: Check what else needs to happen from C side.

        // Initialise the queue depth.
        let max_depth = (u64::from_le(dev.resources().unwrap().bar.readq(OFFSET_CAP)) & 0xffff) + 1;
        let q_depth = core::cmp::min(max_depth, 1024).try_into()?;

        dev.queues.lock().io.try_reserve(nr_io_queues as _)?;
        for i in 1..=nr_io_queues {
            let qid = i.try_into()?;
            let vector = qid % (irqs as u16);

            let io_queue =
                NvmeQueue::try_new(dev.clone(), pci_dev, qid, q_depth, vector, tagset.clone())?;

            // Create completion queue.
            adapter_alloc_cq(mq, &io_queue)?;

            // Create submission queue.
            adapter_alloc_sq(mq, &io_queue)?;

            io_queue.register_irq(pci_dev)?;
            dev.queues.lock().io.try_push(io_queue.clone())?;
        }

        Ok(tagset)
    }

    fn dev_add(
        cap: u64,
        dev: &Ref<DeviceData>,
        pci_dev: &mut pci::Device,
        admin_queue: &Ref<NvmeQueue>,
        mq: &mq::RequestQueue<NvmeDevice>,
    ) -> Result {
        let tagset = Self::setup_io_queues(dev, pci_dev, admin_queue, mq)?;

        let id = dma::try_alloc_coherent::<u8>(pci_dev, 4096, false)?;
        let rt = dma::try_alloc_coherent::<u8>(pci_dev, 4096, false)?;

        // Identify the device.
        nvme_identify(mq, 0, 1, id.dma_handle)?;

        let nn;
        let mdts;
        {
            let ctrl_id = unsafe { &*(id.first_ptr() as *const NvmeIdCtrl) };
            nn = ctrl_id.nn.into();
            mdts = ctrl_id.mdts;
        }

        let max_sectors = if let Some(blocks) = calculate_max_blocks(cap, mdts) {
            core::cmp::min((NVME_MAX_KB_SZ << 1) as u32, blocks)
        } else {
            (NVME_MAX_KB_SZ << 1) as u32
        };
        let zero_rt = NvmeLbaRangeType::default();
        for i in 1..=nn {
            if nvme_identify(mq, i, 0, id.dma_handle).is_err() {
                continue;
            }
            let id_ns = unsafe { &*(id.first_ptr() as *const NvmeIdNs) };
            if id_ns.ncap.into() == 0 {
                continue;
            }

            let res = nvme_get_features(mq, NVME_FEAT_LBA_RANGE, i, rt.dma_handle);
            let rt = if res.is_err() {
                &zero_rt
            } else {
                unsafe { &*(rt.first_ptr() as *const NvmeLbaRangeType) }
            };

            if let Ok(disk) =
                Self::alloc_ns(max_sectors, dev.instance, i, id_ns, tagset.clone(), rt)
            {
                // TODO: Add disk to list.
                pr_info!("about to add disk\n");
                disk.add();
                pr_info!("disk added\n");

                core::mem::forget(disk);
            }
        }

        Ok(())
    }

    fn configure_admin_queue(
        dev: &Ref<DeviceData>,
        pci_dev: &pci::Device,
    ) -> Result<(Ref<NvmeQueue>, mq::RequestQueue<NvmeDevice>)> {
        let admin_tagset = mq::TagSet::try_new(1, dev.clone())?;
        let admin_queue = NvmeQueue::try_new(dev.clone(), pci_dev, 0, 64, 0, admin_tagset.clone())?;
        dev.queues.lock().admin = Some(admin_queue.clone());
        let ns = Box::try_new(NvmeNamespace {
            id: 0,
            lba_shift: 9,
        })?;
        let admin_mq = mq::RequestQueue::try_new(admin_tagset, ns)?;

        let mut aqa = (admin_queue.q_depth - 1) as u32;
        aqa |= aqa << 16;

        let mut ctrl_config = NVME_CC_ENABLE | NVME_CC_CSS_NVM;
        ctrl_config |= (kernel::PAGE_SHIFT - 12) << NVME_CC_MPS_SHIFT;
        ctrl_config |= NVME_CC_ARB_RR | NVME_CC_SHN_NONE;
        ctrl_config |= NVME_CC_IOSQES | NVME_CC_IOCQES;

        {
            let res = dev.resources().unwrap();
            let bar = &res.bar;

            bar.writel(0, OFFSET_CC);
            bar.writel(aqa, OFFSET_AQA);
            bar.writeq(admin_queue.sq.dma_handle, OFFSET_ASQ);
            bar.writeq(admin_queue.cq.dma_handle, OFFSET_ACQ);
            bar.writel(ctrl_config, OFFSET_CC);

            pr_info!("About to wait for nvme readiness\n");
            while u32::from_le(bar.readl(OFFSET_CSTS)) & NVME_CSTS_RDY == 0 {
                unsafe { bindings::msleep(100) };
                // TODO: Add check for fatal signal pending.
                // TODO: Set timeout.
            }

            pr_info!("Done waiting...\n");
        }
        admin_queue.register_irq(pci_dev)?;
        Ok((admin_queue, admin_mq))
    }
}

impl mq::Operations for NvmeDevice {
    type RequestData = NvmeRequest;
    type QueueData = Box<NvmeNamespace>;
    type HwData = Ref<NvmeQueue>;
    type TagSetData = Ref<DeviceData>;

    fn new_request_data(data: RefBorrow<'_, DeviceData>) -> Result<NvmeRequest> {
        Ok(NvmeRequest {
            dma_addr: AtomicU64::new(!0),
            result: AtomicU32::new(0),
            status: AtomicU16::new(0),
            direction: AtomicU32::new(bindings::dma_data_direction_DMA_FROM_DEVICE),
            len: AtomicU32::new(0),
            dev: data.dev.clone(),
            cmd: UnsafeCell::new(NvmeCommand::default()),
            sg_count: AtomicU32::new(0),
            page_count: AtomicU32::new(0),
            first_dma: AtomicU64::new(0),
            mapping_data: AtomicOptionalBoxedPtr::new(None),
            dma_pool: data.dma_pool.clone(),
        })
    }

    fn init_hctx(tagset_data: RefBorrow<'_, DeviceData>, hctx_idx: u32) -> Result<Ref<NvmeQueue>> {
        let queues = tagset_data.queues.lock();
        Ok(if queues.io.len() == 0 {
            queues.admin.as_ref().ok_or(EINVAL)?.clone()
        } else {
            queues.io[hctx_idx as usize].clone()
        })
    }

    fn queue_rq(
        io_queue: RefBorrow<'_, NvmeQueue>,
        ns: &NvmeNamespace,
        rq: &mq::Request<Self>,
        is_last: bool,
    ) -> Result {
        match rq.command() {
            bindings::req_opf_REQ_OP_DRV_IN | bindings::req_opf_REQ_OP_DRV_OUT => {
                io_queue.submit(unsafe { &*rq.data().cmd.get() }, is_last);
                Ok(())
            }
            bindings::req_opf_REQ_OP_FLUSH => {
                let mut cmd = NvmeCommand::new_flush(ns.id);
                cmd.common.command_id = rq.tag() as u16;
                io_queue.submit(&cmd, is_last);
                Ok(())
            }
            bindings::req_opf_REQ_OP_WRITE | bindings::req_opf_REQ_OP_READ => {
                let (direction, opcode) = if rq.command() == bindings::req_opf_REQ_OP_READ {
                    (
                        bindings::dma_data_direction_DMA_FROM_DEVICE,
                        NvmeOpcode::read,
                    )
                } else {
                    (
                        bindings::dma_data_direction_DMA_TO_DEVICE,
                        NvmeOpcode::write,
                    )
                };
                let len = rq.payload_bytes();
                // TODO: Return this from the request.
                let offset = unsafe { (*rq.bio()).bi_iter.bi_sector };
                let mut cmd = NvmeCommand {
                    rw: NvmeRw {
                        opcode: opcode as _,
                        command_id: rq.tag() as u16,
                        nsid: ns.id.into(),
                        slba: (offset >> (ns.lba_shift - bindings::SECTOR_SHIFT)).into(),
                        length: ((len >> ns.lba_shift) as u16 - 1).into(),
                        ..NvmeRw::default()
                    },
                };

                if rq.nr_phys_segments() == 1 {
                    let bv = rq.first_bvec();
                    if (bv.bv_offset % (NVME_CTRL_PAGE_SIZE as u32)) + len
                        <= (NVME_CTRL_PAGE_SIZE * 2) as u32
                    {
                        let dma_addr = unsafe {
                            bindings::dma_map_page_attrs(
                                io_queue.data.dev.ptr,
                                bv.bv_page,
                                bv.bv_offset as _,
                                len as _,
                                direction,
                                0,
                            )
                        };
                        if dma_addr == !0 {
                            return Err(ENOMEM);
                        }

                        rq.start();

                        cmd.rw.prp1 = dma_addr.into();
                        if len > (NVME_CTRL_PAGE_SIZE as u32) {
                            cmd.rw.prp2 = (dma_addr + (NVME_CTRL_PAGE_SIZE as u64)).into();
                        }

                        let pdu = rq.data();
                        pdu.dma_addr.store(dma_addr, Ordering::Relaxed);
                        pdu.direction.store(direction, Ordering::Relaxed);
                        pdu.len.store(len, Ordering::Relaxed);

                        io_queue.submit(&cmd, is_last);
                        return Ok(());
                    }
                }

                let mut md = Box::try_new(MappingData::default())?;
                let count = rq.map_sg(&mut md.sg)?;
                let dev = &io_queue.data.dev;
                dev.dma_map_sg(&mut md.sg[..count as usize], direction)?;
                let page_count = setup_prps(&io_queue.data, &mut cmd, &mut md, len)?;

                let pdu = rq.data();
                pdu.sg_count.store(count, Ordering::Relaxed);
                pdu.page_count.store(page_count, Ordering::Relaxed);
                pdu.first_dma
                    .store(unsafe { cmd.common.prp2.into() }, Ordering::Relaxed);
                pdu.mapping_data.store(Some(md), Ordering::Relaxed);

                rq.start();

                io_queue.submit(&cmd, is_last);
                Ok(())
            }

            _ => Err(EIO),
        }
    }

    fn commit_rqs(io_queue: RefBorrow<'_, NvmeQueue>, _ns: &NvmeNamespace) {
        io_queue.write_sq_db(true, &mut io_queue.inner.lock_irqdisable());
    }

    fn complete(rq: &mq::Request<Self>) {
        match rq.command() {
            bindings::req_opf_REQ_OP_DRV_IN
            | bindings::req_opf_REQ_OP_DRV_OUT
            | bindings::req_opf_REQ_OP_FLUSH => {
                // We just complete right away if flush completes.
                rq.end_ok();
                return;
            }
            _ => {}
        }

        let pdu = rq.data();

        if let Some(mut md) = pdu.mapping_data.take(Ordering::Relaxed) {
            pdu.dev.dma_unmap_sg(
                &mut md.sg[..pdu.sg_count.load(Ordering::Relaxed) as usize],
                pdu.direction.load(Ordering::Relaxed),
            );
            free_prps(
                pdu.page_count.load(Ordering::Relaxed) as _,
                &md.pages,
                pdu.first_dma.load(Ordering::Relaxed),
                &pdu.dma_pool,
            );
        } else {
            // Unmap the page we mapped.
            unsafe {
                bindings::dma_unmap_page_attrs(
                    pdu.dev.ptr,
                    pdu.dma_addr.load(Ordering::Relaxed),
                    pdu.len.load(Ordering::Relaxed) as _,
                    pdu.direction.load(Ordering::Relaxed),
                    0,
                )
            };
        }

        // On failure, complete the request immediately with an error.
        let status = pdu.status.load(Ordering::Relaxed);
        if status != 0 {
            pr_info!("Completing with error {:x}\n", status);
            rq.end_err(EIO);
            return;
        }

        rq.end_ok();
    }
}

fn free_prps(count: usize, pages: &[usize], first_dma: u64, dma_pool: &Ref<dma::Pool<le<u64>>>) {
    let mut dma_addr = first_dma;
    for page in &pages[..count] {
        let prp_list = unsafe {
            dma::CoherentAllocation::<le<u64>, dma::Pool<le<u64>>>::from_parts(
                dma_pool,
                *page,
                dma_addr,
                NVME_CTRL_PAGE_SIZE / 8,
            )
        };

        dma_addr = prp_list.read(NVME_CTRL_PAGE_SIZE / 8 - 1).unwrap().into();
    }
}

fn setup_prps(
    data: &NvmeData,
    cmd: &mut NvmeCommand,
    md: &mut MappingData,
    mut length: u32,
) -> Result<u32> {
    let mut i = 0;
    let mut sg = &md.sg[i];
    let mut dma_addr = sg.dma_address; // TODO: Use macro.
    let mut dma_len = sg.length; // TODO: Use macro.
    let offset = dma_addr & ((NVME_CTRL_PAGE_SIZE - 1) as u64);

    let consumed = ((NVME_CTRL_PAGE_SIZE as u64) - offset) as u32;

    cmd.common.prp1 = dma_addr.into();
    length = length.saturating_sub(consumed);
    if length == 0 {
        return Ok(0);
    }

    dma_len = dma_len.saturating_sub(consumed);
    if dma_len != 0 {
        dma_addr += consumed as u64;
    } else {
        i += 1;
        // TODO: Use sg_next.
        sg = &md.sg[i];
        dma_addr = sg.dma_address;
        dma_len = sg.length;
    }

    if length <= NVME_CTRL_PAGE_SIZE as u32 {
        cmd.common.prp2 = dma_addr.into();
        return Ok(0);
    }

    let mut prp_list = ManuallyDrop::new(data.dma_pool.try_alloc(true)?);

    cmd.common.prp2 = prp_list.dma_handle.into();
    md.pages[0] = prp_list.first_ptr() as usize;
    struct Data<'a> {
        page_count: usize,
        pages: &'a mut [usize],
        first_dma: u64,
    }
    let mut guard = ScopeGuard::new_with_data(
        Data {
            page_count: 1,
            pages: &mut md.pages,
            first_dma: prp_list.dma_handle,
        },
        |g| {
            free_prps(g.page_count, g.pages, g.first_dma, &data.dma_pool);
        },
    );

    let mut j = 0;
    let mut last_dma_addr = 0;
    loop {
        if j == NVME_CTRL_PAGE_SIZE / 8 {
            let new_prp_list = ManuallyDrop::new(data.dma_pool.try_alloc(true)?);
            prp_list.write(NVME_CTRL_PAGE_SIZE / 8 - 1, &new_prp_list.dma_handle.into());
            new_prp_list.write(0, &last_dma_addr.into());
            prp_list = new_prp_list;
            let next = guard.page_count;
            guard.pages[next] = prp_list.first_ptr() as usize;
            guard.page_count += 1;
            j = 1;
        }
        last_dma_addr = dma_addr;
        prp_list.write(j, &dma_addr.into());
        j += 1;

        length = length.saturating_sub(NVME_CTRL_PAGE_SIZE as u32);
        if length == 0 {
            break;
        }

        if dma_len > NVME_CTRL_PAGE_SIZE as u32 {
            dma_addr += NVME_CTRL_PAGE_SIZE as u64;
            dma_len -= NVME_CTRL_PAGE_SIZE as u32;
            continue;
        }

        if dma_len < NVME_CTRL_PAGE_SIZE as u32 {
            // TODO: Write warning.
            return Err(EIO);
        }

        i += 1;
        // TODO: use sg_next.
        sg = &md.sg[i];
        dma_addr = sg.dma_address;
        dma_len = sg.length;
    }

    Ok(guard.dismiss().page_count as _)
}

fn submit_sync_cmd(mq: &mq::RequestQueue<NvmeDevice>, mut cmd: NvmeCommand) -> Result<u32> {
    let op = if unsafe { cmd.common.opcode } & 1 != 0 {
        bindings::req_opf_REQ_OP_DRV_OUT
    } else {
        bindings::req_opf_REQ_OP_DRV_IN
    };
    let rq = mq.alloc_sync_request(op)?;
    cmd.common.command_id = rq.tag() as u16;
    unsafe { rq.data().cmd.get().write(cmd) };

    rq.execute(false)?;

    let pdu = rq.data();
    if pdu.status.load(Ordering::Relaxed) != 0 {
        Err(EIO)
    } else {
        Ok(pdu.result.load(Ordering::Relaxed))
    }
}

fn adapter_alloc_cq(mq: &mq::RequestQueue<NvmeDevice>, queue: &NvmeQueue) -> Result<u32> {
    submit_sync_cmd(
        mq,
        NvmeCommand {
            create_cq: NvmeCreateCq {
                opcode: NvmeAdminOpcode::create_cq as _,
                prp1: queue.cq.dma_handle.into(),
                cqid: queue.qid.into(),
                qsize: (queue.q_depth - 1).into(),
                cq_flags: (NVME_QUEUE_PHYS_CONTIG | NVME_CQ_IRQ_ENABLED).into(),
                irq_vector: queue.cq_vector.into(),
                ..NvmeCreateCq::default()
            },
        },
    )
}

fn adapter_alloc_sq(mq: &mq::RequestQueue<NvmeDevice>, queue: &NvmeQueue) -> Result<u32> {
    submit_sync_cmd(
        mq,
        NvmeCommand {
            create_sq: NvmeCreateSq {
                opcode: NvmeAdminOpcode::create_sq as _,
                prp1: queue.sq.dma_handle.into(),
                sqid: queue.qid.into(),
                qsize: (queue.q_depth - 1).into(),
                sq_flags: (NVME_QUEUE_PHYS_CONTIG | NVME_SQ_PRIO_MEDIUM).into(),
                cqid: queue.qid.into(),
                ..NvmeCreateSq::default()
            },
        },
    )
}

fn nvme_identify(
    mq: &mq::RequestQueue<NvmeDevice>,
    nsid: u32,
    cns: u32,
    dma_addr: u64,
) -> Result<u32> {
    submit_sync_cmd(
        mq,
        NvmeCommand {
            identify: NvmeIdentify {
                opcode: NvmeAdminOpcode::identify as _,
                nsid: nsid.into(),
                prp1: dma_addr.into(),
                cns: cns.into(),
                ..NvmeIdentify::default()
            },
        },
    )
}

fn nvme_get_features(
    mq: &mq::RequestQueue<NvmeDevice>,
    fid: u32,
    nsid: u32,
    dma_addr: u64,
) -> Result<u32> {
    submit_sync_cmd(
        mq,
        NvmeCommand {
            features: NvmeFeatures {
                opcode: NvmeAdminOpcode::get_features as _,
                nsid: nsid.into(),
                prp1: dma_addr.into(),
                fid: fid.into(),
                ..NvmeFeatures::default()
            },
        },
    )
}

fn nvme_set_features(
    mq: &mq::RequestQueue<NvmeDevice>,
    fid: u32,
    dword11: u32,
    dma_addr: u64,
) -> Result<u32> {
    submit_sync_cmd(
        mq,
        NvmeCommand {
            features: NvmeFeatures {
                opcode: NvmeAdminOpcode::set_features as _,
                prp1: dma_addr.into(),
                fid: fid.into(),
                dword11: dword11.into(),
                ..NvmeFeatures::default()
            },
        },
    )
}

fn nvme_dbbuf_set(
    mq: &mq::RequestQueue<NvmeDevice>,
    dbs_dma_addr: u64,
    eis_dma_addr: u64,
) -> Result<u32> {
    submit_sync_cmd(
        mq,
        NvmeCommand {
            common: NvmeCommon {
                opcode: NvmeAdminOpcode::dbbuf as _,
                prp1: dbs_dma_addr.into(),
                prp2: eis_dma_addr.into(),
                ..NvmeCommon::default()
            },
        },
    )
}

impl pci::Driver for NvmeDevice {
    type InnerData = DeviceData;

    declare_pci_id_table! {
        (bindings::PCI_CLASS_STORAGE_EXPRESS, 0xffffff),
    }

    fn probe(dev: &mut pci::Device, _id: &(u32, u32, Option<()>)) -> Result<Ref<DeviceData>> {
        pr_info!("probe called!\n");

        // TODO: We need to disable the device on error.
        dev.enable_device_mem()?;
        dev.set_master();

        let bars = dev.select_bars(bindings::IORESOURCE_MEM.into());

        // TODO: We need to release resources on failure.
        dev.request_selected_regions(bars, c_str!("nvme"))?;

        // TODO: Set the right mask.
        dev.dma_set_mask(!0)?;
        dev.dma_set_coherent_mask(!0)?;

        let res = dev.take_resource(0).ok_or(ENXIO)?;
        let bar = unsafe { IoMem::<8192>::try_new(res) }?;

        // We start off with just one vector. We increase it later.
        dev.alloc_irq_vectors(1, 1, bindings::PCI_IRQ_ALL_TYPES)?;

        let cap = u64::from_le(bar.readq(OFFSET_CAP));
        let mut data = Pin::from(kernel::new_device_data!(
            (),
            NvmeResources { bar },
            NvmeData {
                db_stride: 1 << (((cap >> 32) & 0xf) + 2),
                dev: Device::from_dev(dev),
                instance: 0, // TODO: Initialise instance number.
                shadow: None,
                dma_pool: dma::Pool::try_new(
                    c_str!("prp list page"),
                    dev,
                    NVME_CTRL_PAGE_SIZE / 8,
                    NVME_CTRL_PAGE_SIZE,
                    0,
                )?,
                // SAFETY: `spinlock_init` is called below.
                queues: unsafe {
                    SpinLock::new(NvmeQueues {
                        admin: None,
                        io: Vec::new(),
                    })
                },
            },
            "Nvme::Data"
        )?);

        // SAFETY: Queue vector is pinned when `data` is.
        let queues = unsafe { data.as_mut().map_unchecked_mut(|d| &mut d.queues) };
        kernel::spinlock_init!(queues, "DeviceData::queues");

        let data = Ref::<DeviceData>::from(data);

        let (admin_queue, admin_mq) = Self::configure_admin_queue(&data, dev)?;

        // TODO: Move this to a function. We should not fail `probe` if this fails.
        {
            let dbs = dma::try_alloc_coherent::<u32>(dev, NVME_CTRL_PAGE_SIZE / 4, false)?;
            let eis = dma::try_alloc_coherent::<u32>(dev, NVME_CTRL_PAGE_SIZE / 4, false)?;

            for i in 0..NVME_CTRL_PAGE_SIZE / 4 {
                dbs.write(i, &0);
                eis.write(i, &0);
            }

            if nvme_dbbuf_set(&admin_mq, dbs.dma_handle, eis.dma_handle).is_ok() {
                // TODO: Fix this.
                let x = unsafe { &mut *(&(**data) as *const NvmeData as *mut NvmeData) };
                x.shadow = Some(NvmeShadow { dbs, eis });
            }
        }

        Self::dev_add(cap, &data, dev, &admin_queue, &admin_mq)?;

        pr_info!("Probe succeeded!\n");
        Ok(data)
    }
}

impl irq::Handler for NvmeDevice {
    type Data = Ref<NvmeQueue>;

    fn handle_irq(queue: RefBorrow<'_, NvmeQueue>) -> irq::Return {
        if queue.process_cq() {
            irq::Return::Handled
        } else {
            irq::Return::None
        }
    }
}

struct NvmeQueueInner {
    sq_tail: u16,
    last_sq_tail: u16,

    irq: Option<irq::Registration<NvmeDevice>>,
}

struct NvmeQueue {
    data: Ref<DeviceData>,
    db_offset: usize,
    sdb_index: usize,
    qid: u16,

    cq_head: AtomicU16,
    cq_phase: AtomicU16,

    sq: dma::CoherentAllocation<NvmeCommand, dma::CoherentAllocator>,
    cq: dma::CoherentAllocation<NvmeCompletion, dma::CoherentAllocator>,

    q_depth: u16,
    cq_vector: u16,

    inner: SpinLock<NvmeQueueInner>,
    tagset: Ref<mq::TagSet<NvmeDevice>>,
}

impl NvmeQueue {
    fn try_new(
        data: Ref<DeviceData>,
        dev: &pci::Device,
        qid: u16,
        depth: u16,
        vector: u16,
        tagset: Ref<mq::TagSet<NvmeDevice>>,
    ) -> Result<Ref<Self>> {
        let cq = dma::try_alloc_coherent::<NvmeCompletion>(dev, depth.into(), false)?;
        let sq = dma::try_alloc_coherent(dev, depth.into(), false)?;

        // Zero out all completions. This is necessary so that we can check the phase.
        for i in 0..depth {
            cq.write(i.into(), &NvmeCompletion::default());
        }

        let sdb_offset = (qid as usize) * data.db_stride * 2;
        let db_offset = sdb_offset + 4096;
        let mut queue = Pin::from(UniqueRef::try_new(Self {
            data,
            db_offset,
            sdb_index: sdb_offset / 4,
            qid,
            sq,
            cq,
            q_depth: depth,
            cq_vector: vector,
            tagset,
            cq_head: AtomicU16::new(0),
            cq_phase: AtomicU16::new(1),
            // SAFETY: `spinlock_init` is called below.
            inner: unsafe {
                SpinLock::new(NvmeQueueInner {
                    sq_tail: 0,
                    last_sq_tail: 0,
                    irq: None,
                })
            },
        })?);

        // SAFETY: `inner` is pinned when `queue` is.
        let inner = unsafe { queue.as_mut().map_unchecked_mut(|q| &mut q.inner) };
        kernel::spinlock_init!(inner, "NvmeQueue::inner");

        Ok(queue.into())
    }

    /// Processes the completion queue.
    ///
    /// Returns `true` if at least one entry was processed, `false` otherwise.
    fn process_cq(&self) -> bool {
        let mut head = self.cq_head.load(Ordering::Relaxed);
        let mut phase = self.cq_phase.load(Ordering::Relaxed);
        let mut was_processed = false;

        loop {
            let cqe = self.cq.read_volatile(head.into()).unwrap();
            if cqe.status.into() & 1 != phase {
                break;
            }

            was_processed = true;
            head += 1;
            if head == self.q_depth {
                head = 0;
                phase ^= 1;
            }

            let cmdid = cqe.command_id;

            if let Some(rq) = self
                .tagset
                .tag_to_rq(self.qid.saturating_sub(1).into(), cmdid.into())
            {
                let pdu = rq.data();
                pdu.result.store(cqe.result.into(), Ordering::Relaxed);
                pdu.status.store(cqe.status.into() >> 1, Ordering::Relaxed);
                rq.complete();
            } else {
                pr_warn!("invalid id completed: {}", cmdid);
            }
        }

        if !was_processed {
            return false;
        }

        if self.dbbuf_update_and_check_event(head.into(), self.data.db_stride / 4) {
            if let Some(res) = self.data.resources() {
                let _ = res
                    .bar
                    .try_writel(head.into(), self.db_offset + self.data.db_stride);
            }
        }

        // TODO: Comment on why it's ok.
        self.cq_head.store(head, Ordering::Relaxed);
        self.cq_phase.store(phase, Ordering::Relaxed);

        true
    }

    fn dbbuf_need_event(event_idx: u16, new_idx: u16, old: u16) -> bool {
        new_idx.wrapping_sub(event_idx).wrapping_sub(1) < new_idx.wrapping_sub(old)
    }

    fn dbbuf_update_and_check_event(&self, value: u16, extra_index: usize) -> bool {
        if self.qid == 0 {
            return true;
        }

        let shadow = if let Some(s) = &self.data.shadow {
            s
        } else {
            return true;
        };

        let index = self.sdb_index + extra_index;

        // TODO: This should be a wmb (sfence on x86-64).
        // Ensure that the queue is written before updating the doorbell in memory.
        fence(Ordering::SeqCst);

        let old_value = shadow.dbs.read_write(index, value.into()).unwrap();

        // Ensure that the doorbell is updated before reading the event index from memory. The
        // controller needs to provide similar ordering to ensure the envent index is updated
        // before reading the doorbell.
        fence(Ordering::SeqCst);

        let ei = shadow.eis.read_volatile(index).unwrap();
        Self::dbbuf_need_event(ei as _, value, old_value as _)
    }

    fn write_sq_db(&self, write_sq: bool, inner: &mut NvmeQueueInner) {
        if !write_sq {
            let mut next_tail = inner.sq_tail + 1;
            if next_tail == self.q_depth {
                next_tail = 0;
            }
            if next_tail != inner.last_sq_tail {
                return;
            }
        }

        if self.dbbuf_update_and_check_event(inner.sq_tail, 0) {
            if let Some(res) = self.data.resources() {
                let _ = res.bar.try_writel(inner.sq_tail.into(), self.db_offset);
            }
        }
        inner.last_sq_tail = inner.sq_tail;
    }

    fn submit(&self, cmd: &NvmeCommand, is_last: bool) {
        let mut inner = self.inner.lock_irqdisable();
        self.sq.write(inner.sq_tail.into(), cmd);
        inner.sq_tail += 1;
        if inner.sq_tail == self.q_depth {
            inner.sq_tail = 0;
        }
        self.write_sq_db(is_last, &mut inner);
    }

    fn unregister_irq(&self) {
        self.inner.lock_irqdisable().irq.take();
    }

    fn register_irq(self: &Ref<Self>, pci_dev: &pci::Device) -> Result {
        let irq = pci_dev.request_irq(
            self.cq_vector.into(),
            self.clone(),
            format_args!("nvme{}q{}", self.data.instance, self.qid),
        )?;
        self.inner.lock_irqdisable().irq.replace(irq);
        Ok(())
    }
}

struct NvmeModule {
    _pci: Pin<Box<pci::Registration>>,
}

impl kernel::Module for NvmeModule {
    fn init(_name: &'static CStr, _module: &ThisModule) -> Result<Self> {
        pr_info!("Nvme module loaded!\n");
        static_assert!(core::mem::size_of::<MappingData>() <= kernel::PAGE_SIZE);
        let mut pci = Pin::from(Box::try_new(pci::Registration::new())?);
        pci.as_mut().register::<NvmeDevice>(c_str!("nvme"))?;
        pr_info!("pci driver registered\n");
        Ok(Self { _pci: pci })
    }
}

// TODO: Define PCI module.
module! {
    type: NvmeModule,
    name: b"nvme",
    author: b"Wedson Almeida Filho",
    license: b"GPL v2",
}
