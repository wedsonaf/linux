// SPDX-License-Identifier: GPL-2.0

//! File system based on tar files and an index.

use core::mem::size_of;
use kernel::fs::ro::{
    DirEntryType, INode, INodeParams, INodeType, NewSuperBlock, Super, SuperBlock, SuperParams,
    Time,
};
use kernel::{c_str, folio::LockedFolio, fs, prelude::*, types::ARef, types::Either, types::LE};

kernel::module_ro_fs! {
    type: TarFs,
    name: "tarfs",
    author: "Wedson Almeida Filho <walmeida@microsoft.com>",
    description: "File system for indexed tar files",
    license: "GPL",
}

const SECTOR_SIZE: u64 = 512;
const TARFS_BSIZE: u64 = 4096;
const TARFS_BSIZE_BITS: u8 = 12;

/// An inode in the tarfs inode table.
#[repr(C)]
pub struct Inode {
    /// The mode of the inode.
    ///
    /// The bottom 9 bits are the rwx bits for owner, group, all.
    ///
    /// The bits in the [`S_IFMT`] mask represent the file mode.
    pub mode: LE<u16>,

    /// Tarfs flags for the inode.
    ///
    /// Values are drawn from the [`inode_flags`] module.
    pub flags: u8,

    /// The bottom 4 bits represent the top 4 bits of mtime.
    pub hmtime: u8,

    /// The owner of the inode.
    pub owner: LE<u32>,

    /// The group of the inode.
    pub group: LE<u32>,

    /// The bottom 32 bits of mtime.
    pub lmtime: LE<u32>,

    /// Size of the contents of the inode.
    pub size: LE<u64>,

    /// Either the offset to the data, or the major and minor numbers of a device.
    ///
    /// For the latter, the 32 LSB are the minor, and the 32 MSB are the major numbers.
    pub offset: LE<u64>,
}

/// An entry in a tarfs directory entry table.
#[repr(C)]
pub struct DirEntry {
    /// The inode number this entry refers to.
    pub ino: LE<u64>,

    /// The offset to the name of the entry.
    pub name_offset: LE<u64>,

    /// The length of the name of the entry.
    pub name_len: LE<u64>,

    /// The type of entry.
    pub etype: u8,

    /// Unused padding.
    pub _padding: [u8; 7],
}

/// The super-block of a tarfs instance.
#[repr(C)]
pub struct Header {
    /// The offset to the beginning of the inode-table.
    pub inode_table_offset: LE<u64>,

    /// The number of inodes in the file system.
    pub inode_count: LE<u64>,
}

struct INodeData {
    offset: u64,
    _flags: u8,
}

struct TarFs {
    data_size: u64,
    inode_table_offset: u64,
    inode_count: u64,
}

impl TarFs {
    fn iget(sb: &SuperBlock<Self>, ino: u64) -> Result<ARef<INode<Self>>> {
        // Check that the inode number is valid.
        let h = sb.data();
        if ino == 0 || ino > h.inode_count {
            return Err(ENOENT);
        }

        // Create an inode or find an existing (cached) one.
        let inode = match sb.get_or_create_inode(ino)? {
            Either::Left(existing) => return Ok(existing),
            Either::Right(new) => new,
        };

        // TODO: This requires that inode_table_offset be aligned to BSIZE, and that sizeof(inode)
        // be a divisor of BSIZE. Check these two facts.

        // Load inode details from storage.
        let offset = h.inode_table_offset + (ino - 1) * u64::try_from(size_of::<Inode>())?;

        let bh = sb.bread(offset / TARFS_BSIZE)?;
        let b = bh.data();
        let idata =
            unsafe { &*(&b[(offset & (TARFS_BSIZE - 1)) as usize] as *const _ as *const Inode) };

        let mode = idata.mode.value();

        // Ignore inodes that have unknown mode bits.
        if (u32::from(mode) & !(fs::S_IFMT | 0o777)) != 0 {
            return Err(ENOENT);
        }

        let doffset = idata.offset.value();
        let size = idata.size.value().try_into()?;
        let secs = u64::from(idata.lmtime.value()) | (u64::from(idata.hmtime & 0xf) << 32);
        let typ = match u32::from(mode) & fs::S_IFMT {
            fs::S_IFREG => INodeType::Reg,
            fs::S_IFDIR => INodeType::Dir,
            fs::S_IFLNK => INodeType::Lnk,
            fs::S_IFSOCK => INodeType::Sock,
            fs::S_IFIFO => INodeType::Fifo,
            fs::S_IFCHR => INodeType::Chr((doffset >> 32) as u32, doffset as u32),
            fs::S_IFBLK => INodeType::Blk((doffset >> 32) as u32, doffset as u32),
            _ => return Err(ENOENT),
        };
        inode.init(INodeParams {
            typ,
            mode: mode & 0o777,
            size,
            blocks: (idata.size.value() + TARFS_BSIZE - 1) / TARFS_BSIZE,
            nlink: 1,
            uid: idata.owner.value(),
            gid: idata.group.value(),
            ctime: Time { secs, nsecs: 0 },
            mtime: Time { secs, nsecs: 0 },
            atime: Time { secs, nsecs: 0 },
            value: INodeData {
                offset: doffset,
                _flags: idata.flags,
            },
        })
    }

    fn name_eq(sb: &SuperBlock<Self>, mut name: &[u8], offset: u64) -> Result<bool> {
        for v in sb.read(offset, name.len().try_into()?)? {
            let v = v?;
            let b = v.data();
            if b != &name[..b.len()] {
                return Ok(false);
            }
            name = &name[b.len()..];
        }
        Ok(true)
    }

    fn read_name(sb: &SuperBlock<Self>, mut name: &mut [u8], offset: u64) -> Result<bool> {
        for v in sb.read(offset, name.len().try_into()?)? {
            let v = v?;
            let b = v.data();
            name[..b.len()].copy_from_slice(b);
            name = &mut name[b.len()..];
        }
        Ok(true)
    }
}

impl fs::ro::Type for TarFs {
    type Data = Box<Self>;
    type INodeData = INodeData;
    const NAME: &'static CStr = c_str!("tar");
    const SUPER_TYPE: Super = Super::BlockDev;

    fn fill_super(sb: NewSuperBlock<'_, Self>) -> Result<&SuperBlock<Self>> {
        let sb = sb.init(&SuperParams {
            magic: 0x54415246,
            blocksize_bits: TARFS_BSIZE_BITS,
            maxbytes: fs::MAX_LFS_FILESIZE,
            time_gran: 1000000000,
        })?;

        let scount = sb.sector_count()?;
        if scount < TARFS_BSIZE / SECTOR_SIZE {
            return Err(ENXIO);
        }

        let tarfs = {
            let h = sb.bread(scount * SECTOR_SIZE / TARFS_BSIZE - 1)?;
            let b = h.data();
            // TODO: Make this safe.
            let hdr = unsafe {
                &*(&b[(TARFS_BSIZE - SECTOR_SIZE) as usize] as *const _ as *const Header)
            };

            Box::try_new(TarFs {
                inode_table_offset: hdr.inode_table_offset.value(),
                inode_count: hdr.inode_count.value(),
                data_size: scount.checked_mul(SECTOR_SIZE).ok_or(ERANGE)?,
            })?
        };

        pr_info!("inode_table_offset: {}\n", tarfs.inode_table_offset);
        pr_info!("inode_count: {}\n", tarfs.inode_count);
        pr_info!("data_size: {}\n", tarfs.data_size);

        // Check that the inode table starts within the device data.
        if tarfs.inode_table_offset >= tarfs.data_size {
            return Err(E2BIG);
        }

        // Check that the last inode is within bounds (and that there is no overflow when
        // calculating its offset).
        let offset = tarfs
            .inode_count
            .checked_mul(u64::try_from(size_of::<Inode>())?)
            .ok_or(ERANGE)?
            .checked_add(tarfs.inode_table_offset)
            .ok_or(ERANGE)?;
        if offset > tarfs.data_size {
            return Err(E2BIG);
        }

        let sb = sb.init_data(tarfs)?;
        let root = Self::iget(&sb, 1)?;
        sb.init_root(root)
    }

    fn read_dir(
        inode: &INode<Self>,
        mut pos: i64,
        mut report: impl FnMut(&[u8], i64, u64, DirEntryType) -> bool,
    ) -> Result<i64> {
        let sb = inode.super_block();
        let mut name = Vec::<u8>::new();

        if pos < 0 || pos % size_of::<DirEntry>() as i64 != 0 {
            return Err(ENOENT);
        }

        if pos >= inode.size() {
            return Ok(pos);
        }

        // TODO: We must succeed instead of failing if we managed to update `pos`.
        for v in sb.read(
            inode.data().offset + pos as u64,
            u64::try_from(inode.size())? - pos as u64,
        )? {
            let v = v?;
            let entries = unsafe {
                core::slice::from_raw_parts(
                    &v.data()[0] as *const _ as *const DirEntry,
                    v.data().len() / size_of::<DirEntry>(),
                )
            };

            for e in entries {
                let name_len = usize::try_from(e.name_len.value())?;
                if name_len > name.len() {
                    name.try_resize(name_len, 0)?;
                }

                Self::read_name(sb, &mut name[..name_len], e.name_offset.value())?;

                if !report(
                    &name[..name_len],
                    pos,
                    e.ino.value(),
                    DirEntryType::try_from(u32::from(e.etype))?,
                ) {
                    return Ok(pos);
                }

                pos += size_of::<DirEntry>() as i64;
            }
        }
        Ok(pos)
    }

    fn lookup(parent: &INode<Self>, name: &[u8]) -> Result<ARef<INode<Self>>> {
        let name_len = u64::try_from(name.len())?;
        let sb = parent.super_block();

        for v in sb.read(parent.data().offset, parent.size().try_into()?)? {
            let v = v?;
            let entries = unsafe {
                core::slice::from_raw_parts(
                    &v.data()[0] as *const _ as *const DirEntry,
                    v.data().len() / size_of::<DirEntry>(),
                )
            };

            for e in entries {
                if e.name_len.value() != name_len || e.name_len.value() > usize::MAX as u64 {
                    continue;
                }
                if Self::name_eq(sb, name, e.name_offset.value())? {
                    return Self::iget(sb, e.ino.value());
                }
            }
        }

        Err(ENOENT)
    }

    fn read_folio(inode: &INode<Self>, mut folio: LockedFolio<'_>) -> Result {
        let pos = u64::try_from(folio.pos()).unwrap_or(u64::MAX);
        let size = u64::try_from(inode.size())?;
        let sb = inode.super_block();

        let copied = if pos >= size {
            0
        } else {
            let offset = inode.data().offset.checked_add(pos).ok_or(ERANGE)?;
            let len = core::cmp::min(size - pos, folio.size().try_into()?);
            let mut foffset = 0;
            // TODO: Make sure we don't go beyond the end.
            for v in sb.read(offset, len)? {
                let v = v?;
                folio.write(foffset, v.data())?;
                foffset += v.data().len();
            }
            foffset
        };

        folio.zero_out(copied, folio.size() - copied)?;
        folio.mark_uptodate();
        folio.flush_dcache();

        Ok(())
    }
}
