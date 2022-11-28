//! Rust thread example.

//use core::time::Duration;
//use kernel::delay::coarse_sleep;
use kernel::prelude::*;
//use kernel::sync::{CondVar, Mutex};
use kernel::task::Task;

module! {
    type: Lkp,
    name: "lkp_thread",
    license: "GPL",
}

struct Lkp;

fn thread_body() {
    pr_info!("From thread_body: {}\n", Task::current().pid());
}

fn example() -> Result {
    Task::spawn(fmt!("thread_body"), thread_body)?;
    Task::spawn(fmt!("inline"), || {
        pr_info!("From closure: {}\n", Task::current().pid());
    })?;
    Ok(())
}

impl kernel::Module for Lkp {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        example()?;
        Ok(Lkp)
    }
}
