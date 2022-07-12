//! Scull module in Rust.

use kernel::io_buffer::{IoBufferReader, IoBufferWriter};
use kernel::prelude::*;
use kernel::sync::{Ref, RefBorrow};
use kernel::{file, miscdev};

module! {
    type: Scull,
    name: b"scull",
    license: b"GPL",
}

struct Device {
    number: usize,
    contents: Vec<u8>,
}

struct Scull {
    _dev: Pin<Box<miscdev::Registration<Scull>>>,
}

#[vtable]
impl file::Operations for Scull {
    type OpenData = Ref<Device>;
    type Data = Ref<Device>;

    fn open(context: &Ref<Device>, _file: &file::File) -> Result<Ref<Device>> {
        pr_info!("File for device {} was opened\n", context.number);
        Ok(context.clone())
    }

    fn read(
        data: RefBorrow<'_, Device>,
        _file: &file::File,
        _writer: &mut impl IoBufferWriter,
        _offset: u64,
    ) -> Result<usize> {
        pr_info!("File for device {} was read\n", data.number);
        Ok(0)
    }

    fn write(
        data: RefBorrow<'_, Device>,
        _file: &file::File,
        reader: &mut impl IoBufferReader,
        _offset: u64,
    ) -> Result<usize> {
        pr_info!("File for device {} was written\n", data.number);
        let copy = reader.read_all()?;
        data.contents = copy;
        Ok(copy.len())
    }
}

impl kernel::Module for Scull {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        pr_info!("Hello world!\n");
        let dev = Ref::try_new(Device {
            number: 0,
            contents: Vec::new(),
        })?;
        let reg = miscdev::Registration::new_pinned(fmt!("scull"), dev)?;
        Ok(Self { _dev: reg })
    }
}
