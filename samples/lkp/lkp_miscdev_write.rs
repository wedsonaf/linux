//! Rust miscdev registration with write implementation.

use kernel::io_buffer::{IoBufferReader, IoBufferWriter};
use kernel::prelude::*;
use kernel::sync::smutex::Mutex;
use kernel::sync::{Arc, ArcBorrow};
use kernel::{file, miscdev::Registration};

module! {
    type: Lkp,
    name: "lkp_miscdev_write",
    license: "GPL",
}

struct Lkp {
    _reg: Pin<Box<Registration<Self>>>,
}

struct DevState {
    number: u32,
    contents: Mutex<Vec<u8>>,
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
        let contents = data.contents.lock();
        if offset >= contents.len().try_into()? {
            return Ok(0);
        }
        let b = &contents[offset.try_into()?..];
        writer.write_slice(b)?;
        Ok(b.len())
    }

    fn write(
        data: ArcBorrow<'_, DevState>,
        _file: &file::File,
        reader: &mut impl IoBufferReader,
        _offset: u64,
    ) -> Result<usize> {
        let new_data = reader.read_all()?;
        let len = new_data.len();
        *data.contents.lock() = new_data;
        Ok(len)
    }
}

impl kernel::Module for Lkp {
    fn init(name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        let dev_state = Arc::try_new(DevState {
            number: 1,
            contents: Mutex::new(Vec::new()),
        })?;
        Ok(Lkp {
            _reg: Registration::new_pinned(fmt!("{name}"), dev_state)?,
        })
    }
}
