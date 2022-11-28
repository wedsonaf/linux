//! Rust minimal hello world.

use kernel::prelude::*;

module! {
    type: Hello,
    name: "lkp_hello",
    license: "GPL",
}

struct Hello;

impl kernel::Module for Hello {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        pr_info!("Hello world\n");
        Ok(Hello)
    }
}
