//! Rust miscdev registration with allocated device state.

use kernel::prelude::*;
use kernel::{file, miscdev::Registration};

module! {
    type: Lkp,
    name: "lkp_miscdev_box",
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
        Err(ECONNREFUSED)
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
