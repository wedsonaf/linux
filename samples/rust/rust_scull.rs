//! Scull module in Rust.

use kernel::prelude::*;

module! {
    type: Scull,
    name: b"scull",
    license: b"GPL",
}

struct Scull;

impl kernel::Module for Scull {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        Ok(Self)
    }
}
