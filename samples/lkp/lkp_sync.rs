//! Rust synchronization primitives example.

//use core::time::Duration;
//use kernel::delay::coarse_sleep;
use kernel::prelude::*;
use kernel::sync::{Mutex, RawSpinLock, RwSemaphore, SpinLock};

module! {
    type: Lkp,
    name: "lkp_sync",
    license: "GPL",
}

struct Lkp;

kernel::init_static_sync! {
    static MUTEX: Mutex<u32> = 10;
    static SPINLOCK: SpinLock<u32> = 11;
    static RAWSPINLOCK: RawSpinLock<u32> = 12;
    static RWSEMAPHORE: RwSemaphore<u32> = 13;
}

fn example_mutex(m: &Mutex<u32>) {
    let mut guard = m.lock();
    *guard += 1;
    pr_info!("{}\n", *guard);
}

fn example_spinlock(s: &SpinLock<u32>) {
    {
        let mut guard = s.lock();
        *guard += 1;
        pr_info!("{}\n", *guard);
    }

    {
        let mut guard = s.lock_irqdisable();
        *guard += 1;
        pr_info!("{}\n", *guard);
    }
}

fn example_rawspinlock(s: &RawSpinLock<u32>) {
    {
        let mut guard = s.lock();
        *guard += 1;
        pr_info!("{}\n", *guard);
    }

    {
        let mut guard = s.lock_irqdisable();
        *guard += 1;
        pr_info!("{}\n", *guard);
    }
}

fn example_rwsema(s: &RwSemaphore<u32>) {
    {
        let guard = s.read();
        pr_info!("{}\n", *guard);
    }

    {
        let mut guard = s.write();
        *guard += 1;
        pr_info!("{}\n", *guard);
    }
}

fn example() -> Result {
    example_mutex(&MUTEX);
    example_spinlock(&SPINLOCK);
    example_rawspinlock(&RAWSPINLOCK);
    example_rwsema(&RWSEMAPHORE);
    Ok(())
}

impl kernel::Module for Lkp {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        example()?;
        Ok(Lkp)
    }
}
