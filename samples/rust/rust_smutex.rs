// SPDX-License-Identifier: GPL-2.0

//! Rust simple mutex device sample.

use kernel::prelude::*;
use kernel::{
    file::{self, File},
    io_buffer::{IoBufferReader, IoBufferWriter},
    miscdev,
    str::CString,
    sync::{smutex::Mutex, Ref, RefBorrow},
};

module! {
    type: RustSimpleMutex,
    name: b"rust_smutex",
    author: b"Rust for Linux Contributors",
    description: b"Rust simple mutex device sample",
    license: b"GPL v2",
}

struct SharedState {
    count: Mutex<u64>,
}

impl file::Operations for SharedState {
    type Data = Ref<SharedState>;
    type OpenData = Ref<SharedState>;

    kernel::declare_file_operations!(read, write);

    fn open(shared: &Ref<SharedState>, _file: &File) -> Result<Self::Data> {
        Ok(shared.clone())
    }

    fn read(
        shared: RefBorrow<'_, SharedState>,
        _: &File,
        data: &mut impl IoBufferWriter,
        offset: u64,
    ) -> Result<usize> {
        if offset != 0 {
            return Ok(0);
        }

        let v = *shared.count.lock();
        let s = CString::try_from_fmt(fmt!("{v}\n"))?;
        data.write_slice(s.as_bytes())?;
        Ok(s.len())
    }

    fn write(
        shared: RefBorrow<'_, SharedState>,
        _: &File,
        data: &mut impl IoBufferReader,
        _offset: u64,
    ) -> Result<usize> {
        for _ in 0..100_000_000 {
            *shared.count.lock() += 1;
        }
        Ok(data.len())
    }
}

struct RustSimpleMutex {
    _dev: Pin<Box<miscdev::Registration<SharedState>>>,
}

impl kernel::Module for RustSimpleMutex {
    fn init(name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        pr_info!("Rust simple mutex device sample (init)\n");

        let state = Ref::try_new(SharedState {
            count: Mutex::new(0),
        })?;

        Ok(Self {
            _dev: miscdev::Registration::new_pinned(fmt!("{name}"), state)?,
        })
    }
}
