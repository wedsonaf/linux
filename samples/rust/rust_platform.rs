// SPDX-License-Identifier: GPL-2.0

//! Rust platform device driver sample.

use core::pin::Pin;
use core::sync::atomic::{AtomicU32, Ordering};
use kernel::{
    file, file::File, io_buffer, io_mem, miscdev, mm, module_platform_driver, of, platform,
    prelude::*, sync::Ref, sync::RefBorrow, sync::RevocableRwSemaphore, sync::UniqueRef,
};

module_platform_driver! {
    type: Driver,
    name: b"open_dice",
    license: b"GPL v2",
}

struct Data {
    misc: miscdev::Registration<Driver>,
    res: io_mem::Resource,
}

type DeviceData = RevocableRwSemaphore<Data>;

struct Driver;
impl file::Operations for Driver {
    type Data = Ref<DeviceData>;
    type OpenData = Ref<DeviceData>;

    kernel::declare_file_operations!(read, write, mmap);

    fn open(context: &Ref<DeviceData>, _file: &File) -> Result<Ref<DeviceData>> {
        Ok(context.clone())
    }

    fn read(
        this: RefBorrow<'_, DeviceData>,
        _: &File,
        data: &mut impl io_buffer::IoBufferWriter,
        offset: u64,
    ) -> Result<usize> {
        let guard = this.try_read().ok_or(ENXIO)?;
        let value: u32 = guard.res.size().try_into()?;
        data.write_with_offset(offset, &value)
    }

    fn write(
        this: RefBorrow<'_, DeviceData>,
        _file: &File,
        data: &mut impl io_buffer::IoBufferReader,
        _offset: u64,
    ) -> Result<usize> {
        let guard = this.try_write().ok_or(ENXIO)?;
        let mut mem = unsafe { io_mem::Remapped::try_new_wc(&guard.res) }?;
        unsafe { mem.as_slice_mut() }.fill(0);
        Ok(data.len())
    }

    fn mmap(data: RefBorrow<'_, DeviceData>, _file: &File, vma: &mut mm::virt::Area) -> Result {
        let mut flags = vma.flags();
        use mm::virt::flags::*;
        // TODO: Check that this is indeed what we meant. It seems like we want an OR between the
        // checks below. Or perhaps we want to prevent writes only when it's shared?
        if flags & WRITE != 0 && flags & SHARED != 0 {
            return Err(EPERM);
        }
        flags |= DONTCOPY | DONTDUMP;
        vma.set_flags(flags);
        // TODO: Set protections to write-combine.
        let guard = data.try_read().ok_or(ENXIO)?;
        vma.iomap_memory(&guard.res)
    }
}

impl platform::Driver for Driver {
    type Data = Ref<DeviceData>;

    kernel::define_of_id_table! {(), [
        (of::DeviceId::Compatible(b"arm,psci"), None),
    ]}

    fn probe(dev: &mut platform::Device, _id_info: Option<&Self::IdInfo>) -> Result<Self::Data> {
        static DEV_IDX: AtomicU32 = AtomicU32::new(0);
        let rmem = if let Some(r) = dev.take_reserved_mem() {
            r
        } else {
            dev_err!(dev, "failed to lookup reserved memory\n");
            return Err(EINVAL);
        };

        if !rmem.is_page_aligned() {
            dev_err!(dev, "memory region must be page-aligned\n");
            return Err(EINVAL);
        }

        // SAFETY: `revocable_init` is called below.
        let mut data = Pin::from(UniqueRef::<DeviceData>::try_new(unsafe {
            RevocableRwSemaphore::new(Data {
                res: rmem,
                misc: miscdev::Registration::new(),
            })
        })?);

        kernel::revocable_init!(data.as_mut(), "OpenDice::Data");

        let data = Ref::<DeviceData>::from(data);

        let mut guard = data.try_write().ok_or(ENXIO)?;
        // SAFETY: `misc` is pinned when `Data` is.
        let pinned = unsafe { guard.as_pinned_mut().map_unchecked_mut(|d| &mut d.misc) };
        miscdev::Options::new().parent(dev).mode(0o600).register(
            pinned,
            fmt!("open-dice{}", DEV_IDX.fetch_add(1, Ordering::Relaxed)),
            data.clone(),
        )?;
        drop(guard);

        Ok(data)
    }
}
