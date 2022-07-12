//! Scull module in Rust.

use kernel::prelude::*;
use kernel::file;

module! {
    type: Scull,
    name: b"scull",
    license: b"GPL",
}

struct Scull;

#[vtable]
impl file::Operations for Scull {
    fn open(_context: &(), _file: &file::File) -> Result {
        pr_info!("File was opened\n");
        Ok(())
    }
}

impl kernel::Module for Scull {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        pr_info!("Hello world!\n");
        Ok(Self)
    }
}
