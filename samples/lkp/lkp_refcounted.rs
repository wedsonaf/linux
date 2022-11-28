//! Rust ref-counted allocations.

use kernel::prelude::*;
use kernel::sync::{Arc, ArcBorrow};

module! {
    type: Lkp,
    name: "lkp_refcounted",
    license: "GPL",
}

struct Lkp;

struct DevState {
    number: u32,
}

fn example() -> Result {
    let stack = DevState { number: 1 };
    let regular = Box::try_new(DevState { number: 1 })?;
    let refcounted = Arc::try_new(DevState { number: 1 })?;
    example1(&stack);
    example1(&regular);
    example1(&refcounted);
    example2(refcounted.clone());
    example3(refcounted.as_arc_borrow());
    Ok(())
}

fn example1(d: &DevState) {
    pr_info!("{}\n", d.number);
    // Cannot call example2 because we can't know if it's ref-counted.
}

fn example2(d: Arc<DevState>) {
    pr_info!("{}\n", d.number);
}

fn example3(d: ArcBorrow<'_, DevState>) {
    example2(d.into());
}

impl kernel::Module for Lkp {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        example()?;
        Ok(Lkp)
    }
}
