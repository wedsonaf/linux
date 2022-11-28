//! Rust miscdev registration with reading from shared state.

use kernel::io_buffer::IoBufferWriter;
use kernel::prelude::*;
use kernel::sync::{Arc, ArcBorrow};
use kernel::{file, miscdev::Registration};

module! {
    type: Lkp,
    name: "lkp_miscdev_arc_read",
    license: "GPL",
}

struct Lkp {
    _reg: Pin<Box<Registration<Self>>>,
}

struct DevState {
    number: u32,
    contents: &'static [u8],
}

#[vtable]
impl file::Operations for Lkp {
    type OpenData = Arc<DevState>;
    type Data = Arc<DevState>;
    fn open(context: &Arc<DevState>, _file: &file::File) -> Result<Self::Data> {
        pr_info!("open on device {}\n", context.number);
        Ok(context.clone())
    }

    fn read(
        data: ArcBorrow<'_, DevState>,
        _file: &file::File,
        writer: &mut impl IoBufferWriter,
        offset: u64,
    ) -> Result<usize> {
        if offset >= data.contents.len().try_into()? {
            return Ok(0);
        }
        let b = &data.contents[offset.try_into()?..];
        writer.write_slice(b)?;
        Ok(b.len())
    }
}

impl kernel::Module for Lkp {
    fn init(name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        let dev_state = Arc::try_new(DevState {
            number: 1,
            contents: b"my file data",
        })?;
        Ok(Lkp {
            _reg: Registration::new_pinned(fmt!("{name}"), dev_state)?,
        })
    }
}
