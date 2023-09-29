// SPDX-License-Identifier: GPL-2.0

//! Rust read-only file system sample.

use kernel::fs::sb;
use kernel::prelude::*;
use kernel::{c_str, fs};

kernel::module_fs! {
    type: RoFs,
    name: "rust_rofs",
    author: "Rust for Linux Contributors",
    description: "Rust read-only file system sample",
    license: "GPL",
}

struct RoFs;
impl fs::FileSystem for RoFs {
    const NAME: &'static CStr = c_str!("rust-fs");

    fn super_params(_sb: &sb::SuperBlock<Self>) -> Result<sb::Params> {
        Ok(sb::Params {
            magic: 0x52555354,
            blocksize_bits: 12,
            maxbytes: fs::MAX_LFS_FILESIZE,
            time_gran: 1,
        })
    }
}
