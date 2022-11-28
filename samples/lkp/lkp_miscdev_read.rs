//! Rust miscdev registration with read implementation.

use kernel::io_buffer::IoBufferWriter;
use kernel::prelude::*;
use kernel::{file, miscdev::Registration};

module! {
    type: Lkp,
    name: "lkp_miscdev_read",
    license: "GPL",
}

struct Lkp {
    _reg: Pin<Box<Registration<Self>>>,
}

struct DevState {
    number: u32,
}

#[vtable]
impl file::Operations for Lkp {
    type OpenData = Box<DevState>;
    fn open(context: &Box<DevState>, _file: &file::File) -> Result<Self::Data> {
        pr_info!("open on device {}\n", context.number);
        Ok(())
    }

    fn read(
        _data: (),
        _file: &file::File,
        writer: &mut impl IoBufferWriter,
        offset: u64,
    ) -> Result<usize> {
        const DATA: &[u8] = b"my file data\n";
        if offset >= DATA.len().try_into()? {
            return Ok(0);
        }
        let b = &DATA[offset.try_into()?..];
        writer.write_slice(b)?;
        Ok(b.len())
    }
}

impl kernel::Module for Lkp {
    fn init(name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        let dev_state = Box::try_new(DevState { number: 1 })?;
        Ok(Lkp {
            _reg: Registration::new_pinned(fmt!("{name}"), dev_state)?,
        })
    }
}
