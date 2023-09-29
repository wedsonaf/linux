// SPDX-License-Identifier: GPL-2.0

//! Rust read-only file system sample.

use kernel::fs::{
    DirEmitter, INode, INodeParams, INodeType, NewSuperBlock, SuperBlock, SuperParams,
};
use kernel::prelude::*;
use kernel::{c_str, fs, time::UNIX_EPOCH, types::ARef, types::Either};

kernel::module_fs! {
    type: RoFs,
    name: "rust_rofs",
    author: "Rust for Linux Contributors",
    description: "Rust read-only file system sample",
    license: "GPL",
}

struct Entry {
    name: &'static [u8],
    ino: u64,
    etype: INodeType,
}

const ENTRIES: [Entry; 3] = [
    Entry {
        name: b".",
        ino: 1,
        etype: INodeType::Dir,
    },
    Entry {
        name: b"..",
        ino: 1,
        etype: INodeType::Dir,
    },
    Entry {
        name: b"subdir",
        ino: 2,
        etype: INodeType::Dir,
    },
];

struct RoFs;
impl fs::FileSystem for RoFs {
    const NAME: &'static CStr = c_str!("rust-fs");

    fn super_params(_sb: &NewSuperBlock<Self>) -> Result<SuperParams> {
        Ok(SuperParams {
            magic: 0x52555354,
            blocksize_bits: 12,
            maxbytes: fs::MAX_LFS_FILESIZE,
            time_gran: 1,
        })
    }

    fn init_root(sb: &SuperBlock<Self>) -> Result<ARef<INode<Self>>> {
        match sb.get_or_create_inode(1)? {
            Either::Left(existing) => Ok(existing),
            Either::Right(new) => new.init(INodeParams {
                typ: INodeType::Dir,
                mode: 0o555,
                size: ENTRIES.len().try_into()?,
                blocks: 1,
                nlink: 2,
                uid: 0,
                gid: 0,
                atime: UNIX_EPOCH,
                ctime: UNIX_EPOCH,
                mtime: UNIX_EPOCH,
            }),
        }
    }

    fn read_dir(inode: &INode<Self>, emitter: &mut DirEmitter) -> Result {
        if inode.ino() != 1 {
            return Ok(());
        }

        let pos = emitter.pos();
        if pos >= ENTRIES.len().try_into()? {
            return Ok(());
        }

        for e in ENTRIES.iter().skip(pos.try_into()?) {
            if !emitter.emit(1, e.name, e.ino, e.etype.into()) {
                break;
            }
        }

        Ok(())
    }
}
