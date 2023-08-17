// SPDX-License-Identifier: GPL-2.0

//! Rust read-only file system sample.

use kernel::fs::ro::{
    DirEntryType, INode, INodeParams, INodeType, NewSuperBlock, SuperBlock, SuperParams, Time,
};
use kernel::prelude::*;
use kernel::{c_str, folio::LockedFolio, fs, types::ARef, types::Either};

kernel::module_ro_fs! {
    type: RoFs,
    name: "rust_rofs",
    author: "Rust for Linux Contributors",
    description: "Rust read-only file system sample",
    license: "GPL",
}

const DATA2: &[u8] = b"hello\n";
const DATA3: &[u8] = b"./test.txt";

struct RoFs;
impl fs::ro::Type for RoFs {
    type Data = ();
    type INodeData = ();
    const NAME: &'static CStr = c_str!("rust-fs");

    fn fill_super(sb: NewSuperBlock<'_, Self>) -> Result<&SuperBlock<Self>> {
        let sb = sb.init(&SuperParams::DEFAULT)?;
        let root = sb.create_inode(1)?.init(INodeParams {
            typ: INodeType::Dir,
            mode: 0o555,
            size: 2,
            blocks: 1,
            nlink: 2,
            uid: 0,
            gid: 0,
            ctime: Time { secs: 0, nsecs: 0 },
            mtime: Time { secs: 0, nsecs: 0 },
            atime: Time { secs: 0, nsecs: 0 },
            value: (),
        })?;
        sb.init_root((), root)
    }

    fn read_dir(
        inode: &INode<Self>,
        mut pos: i64,
        mut report: impl FnMut(&[u8], i64, u64, DirEntryType) -> bool,
    ) -> Result<i64> {
        if inode.ino() != 1 {
            return Ok(pos);
        }

        if pos == 0 {
            if !report(b"test.txt", pos, 2, DirEntryType::Reg) {
                return Ok(pos);
            }
            pos += 1;
        }

        if pos == 1 {
            if !report(b"link.txt", pos, 3, DirEntryType::Lnk) {
                return Ok(pos);
            }
            pos += 1;
        }

        Ok(pos)
    }

    fn lookup(parent: &INode<Self>, name: &[u8]) -> Result<ARef<INode<Self>>> {
        if parent.ino() != 1 {
            return Err(ENOENT);
        }

        match name {
            b"test.txt" => match parent.super_block().get_or_create_inode(2)? {
                Either::Left(existing) => Ok(existing),
                Either::Right(new) => new.init(INodeParams {
                    mode: 0o444,
                    typ: INodeType::Reg,
                    size: DATA2.len().try_into()?,
                    blocks: 1,
                    nlink: 1,
                    uid: 0,
                    gid: 0,
                    ctime: Time { secs: 0, nsecs: 0 },
                    mtime: Time { secs: 0, nsecs: 0 },
                    atime: Time { secs: 0, nsecs: 0 },
                    value: (),
                }),
            },
            b"link.txt" => match parent.super_block().get_or_create_inode(3)? {
                Either::Left(existing) => Ok(existing),
                Either::Right(new) => new.init(INodeParams {
                    mode: 0o444,
                    typ: INodeType::Lnk,
                    size: DATA3.len().try_into()?,
                    blocks: 1,
                    nlink: 1,
                    uid: 0,
                    gid: 0,
                    ctime: Time { secs: 0, nsecs: 0 },
                    mtime: Time { secs: 0, nsecs: 0 },
                    atime: Time { secs: 0, nsecs: 0 },
                    value: (),
                }),
            },
            _ => Err(ENOENT),
        }
    }

    fn read_folio(inode: &INode<Self>, mut folio: LockedFolio<'_>) -> Result {
        let data = match inode.ino() {
            2 => DATA2,
            3 => DATA3,
            _ => return Err(EINVAL),
        };

        let pos = usize::try_from(folio.pos()).unwrap_or(usize::MAX);
        let copied = if pos >= data.len() {
            0
        } else {
            let to_copy = core::cmp::min(data.len() - pos, folio.size());
            folio.write(0, &data[pos..][..to_copy])?;
            to_copy
        };

        folio.zero_out(copied, folio.size() - copied)?;
        folio.mark_uptodate();
        folio.flush_dcache();

        Ok(())
    }
}
