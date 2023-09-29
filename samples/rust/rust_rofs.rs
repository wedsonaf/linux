// SPDX-License-Identifier: GPL-2.0

//! Rust read-only file system sample.

use kernel::fs::{dentry, inode, sb, sb::SuperBlock};
use kernel::prelude::*;
use kernel::{c_str, fs, time::UNIX_EPOCH, types::Either};

kernel::module_fs! {
    type: RoFs,
    name: "rust_rofs",
    author: "Rust for Linux Contributors",
    description: "Rust read-only file system sample",
    license: "GPL",
}

struct RoFs;
impl fs::FileSystem for RoFs {
    const NAME: &'static CStr = c_str!("rust_rofs");

    fn super_params(_sb: &SuperBlock<Self>) -> Result<sb::Params> {
        Ok(sb::Params {
            magic: 0x52555354,
            blocksize_bits: 12,
            maxbytes: fs::MAX_LFS_FILESIZE,
            time_gran: 1,
        })
    }

    fn init_root(sb: &SuperBlock<Self>) -> Result<dentry::Root<Self>> {
        let inode = match sb.get_or_create_inode(1)? {
            Either::Left(existing) => existing,
            Either::Right(new) => new.init(inode::Params {
                typ: inode::Type::Dir,
                mode: 0o555,
                size: 1,
                blocks: 1,
                nlink: 2,
                uid: 0,
                gid: 0,
                atime: UNIX_EPOCH,
                ctime: UNIX_EPOCH,
                mtime: UNIX_EPOCH,
            })?,
        };
        dentry::Root::try_new(inode)
    }
}
