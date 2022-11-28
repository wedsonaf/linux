//! Rust miscdev registration.

use kernel::prelude::*;
use kernel::{file, miscdev::Registration};

module! {
    type: Lkp,
    name: "lkp_miscdev",
    license: "GPL",
}

struct Lkp {
    _reg: Pin<Box<Registration<Self>>>,
}

#[vtable]
impl file::Operations for Lkp {
    fn open(_context: &(), _file: &file::File) -> Result<Self::Data> {
        Err(ECONNREFUSED)
    }
}

impl kernel::Module for Lkp {
    fn init(name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        Ok(Lkp {
            _reg: Registration::new_pinned(fmt!("{name}"), ())?,
        })
    }
}
