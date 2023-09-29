// SPDX-License-Identifier: GPL-2.0

//! File system based on tar files and an index.

use core::mem::size_of;
use defs::*;
use kernel::fs::{
    self, address_space, dentry, dentry::DEntry, file, file::File, inode, inode::INode,
    inode::Type, iomap, sb, sb::SuperBlock, Offset, Stat,
};
use kernel::types::{ARef, Either, FromBytes};
use kernel::{c_str, folio::Folio, prelude::*, str::CString, user};

pub mod defs;

kernel::module_fs! {
    type: TarFs,
    name: "tarfs",
    author: "Wedson Almeida Filho <walmeida@microsoft.com>",
    description: "File system for indexed tar files",
    license: "GPL",
}

const SECTOR_SIZE: u64 = 512;
const TARFS_BSIZE: u64 = 1 << TARFS_BSIZE_BITS;
const TARFS_BSIZE_BITS: u8 = 12;
const SECTORS_PER_BLOCK: u64 = TARFS_BSIZE / SECTOR_SIZE;
const TARFS_MAGIC: u32 = 0x54415246;

static_assert!(SECTORS_PER_BLOCK > 0);

struct INodeData {
    offset: u64,
    flags: u8,
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
        let mut inode = match sb.get_or_create_inode(ino)? {
            Either::Left(existing) => return Ok(existing),
            Either::Right(new) => new,
        };

        static_assert!((TARFS_BSIZE as usize) % size_of::<Inode>() == 0);

        // Load inode details from storage.
        let offset = h.inode_table_offset + (ino - 1) * u64::try_from(size_of::<Inode>())?;

        let bh = sb.bread(offset / TARFS_BSIZE)?;
        let b = bh.data();
        let idata = Inode::from_bytes(b, (offset & (TARFS_BSIZE - 1)) as usize).ok_or(EIO)?;

        let mode = idata.mode.value();

        // Ignore inodes that have unknown mode bits.
        if (mode & !(fs::mode::S_IFMT | 0o777)) != 0 {
            return Err(ENOENT);
        }

        const DIR_FOPS: file::Ops<TarFs> = file::Ops::new::<TarFs>();
        const DIR_IOPS: inode::Ops<TarFs> = inode::Ops::new::<TarFs>();
        const FILE_AOPS: address_space::Ops<TarFs> = iomap::ro_aops::<TarFs>();

        let size = idata.size.value();
        let doffset = idata.offset.value();
        let secs = u64::from(idata.lmtime.value()) | (u64::from(idata.hmtime & 0xf) << 32);
        let ts = kernel::time::Timespec::new(secs, 0)?;
        let typ = match mode & fs::mode::S_IFMT {
            fs::mode::S_IFREG => {
                inode
                    .set_fops(file::Ops::generic_ro_file())
                    .set_aops(FILE_AOPS);
                Type::Reg
            }
            fs::mode::S_IFDIR => {
                inode.set_iops(DIR_IOPS).set_fops(DIR_FOPS);
                Type::Dir
            }
            fs::mode::S_IFLNK => {
                inode.set_iops(inode::Ops::simple_symlink_inode());
                Type::Lnk(Some(Self::get_link(sb, doffset, size)?))
            }
            fs::mode::S_IFSOCK => Type::Sock,
            fs::mode::S_IFIFO => Type::Fifo,
            fs::mode::S_IFCHR => Type::Chr((doffset >> 32) as u32, doffset as u32),
            fs::mode::S_IFBLK => Type::Blk((doffset >> 32) as u32, doffset as u32),
            _ => return Err(ENOENT),
        };
        inode.init(inode::Params {
            typ,
            mode: mode & 0o777,
            size: size.try_into()?,
            blocks: (idata.size.value() + TARFS_BSIZE - 1) / TARFS_BSIZE,
            nlink: 1,
            uid: idata.owner.value(),
            gid: idata.group.value(),
            ctime: ts,
            mtime: ts,
            atime: ts,
            value: INodeData {
                offset: doffset,
                flags: idata.flags,
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

    fn read_name(sb: &SuperBlock<Self>, mut name: &mut [u8], offset: u64) -> Result {
        for v in sb.read(offset, name.len().try_into()?)? {
            let v = v?;
            let b = v.data();
            name[..b.len()].copy_from_slice(b);
            name = &mut name[b.len()..];
        }
        Ok(())
    }

    fn get_link(sb: &SuperBlock<Self>, offset: u64, len: u64) -> Result<CString> {
        let name_len: usize = len.try_into()?;
        let mut name = Box::try_new_slice(name_len.checked_add(1).ok_or(ENOMEM)?, b'\0')?;
        Self::read_name(sb, &mut name[..name_len], offset)?;
        Ok(name.try_into()?)
    }
}

impl fs::FileSystem for TarFs {
    type Data = Box<Self>;
    type INodeData = INodeData;
    const NAME: &'static CStr = c_str!("tar");
    const SUPER_TYPE: sb::Type = sb::Type::BlockDev;

    fn super_params(sb: &SuperBlock<Self, sb::New>) -> Result<sb::Params<Self::Data>> {
        let scount = sb.sector_count();
        if scount < SECTORS_PER_BLOCK {
            pr_err!("Block device is too small: sector count={scount}\n");
            return Err(ENXIO);
        }

        let tarfs = {
            let mut folio = Folio::try_new(0)?;
            sb.sread(
                (scount / SECTORS_PER_BLOCK - 1) * SECTORS_PER_BLOCK,
                SECTORS_PER_BLOCK as usize,
                &mut folio,
            )?;
            let mapped = folio.map(0)?;
            let hdr =
                Header::from_bytes(&mapped, (TARFS_BSIZE - SECTOR_SIZE) as usize).ok_or(EIO)?;
            Box::try_new(TarFs {
                inode_table_offset: hdr.inode_table_offset.value(),
                inode_count: hdr.inode_count.value(),
                data_size: scount.checked_mul(SECTOR_SIZE).ok_or(ERANGE)?,
            })?
        };

        // Check that the inode table starts within the device data and is aligned to the block
        // size.
        if tarfs.inode_table_offset >= tarfs.data_size {
            pr_err!(
                "inode table offset beyond data size: {} >= {}\n",
                tarfs.inode_table_offset,
                tarfs.data_size
            );
            return Err(E2BIG);
        }

        if tarfs.inode_table_offset % SECTOR_SIZE != 0 {
            pr_err!(
                "inode table offset not aligned to sector size: {}\n",
                tarfs.inode_table_offset,
            );
            return Err(EDOM);
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
            pr_err!(
                "inode table extends beyond the data size : {} > {}\n",
                tarfs.inode_table_offset + (tarfs.inode_count * size_of::<Inode>() as u64),
                tarfs.data_size,
            );
            return Err(E2BIG);
        }

        Ok(sb::Params {
            magic: TARFS_MAGIC,
            blocksize_bits: TARFS_BSIZE_BITS,
            maxbytes: fs::MAX_LFS_FILESIZE,
            time_gran: 1000000000,
            data: tarfs,
        })
    }

    fn init_root(sb: &SuperBlock<Self>) -> Result<dentry::Root<Self>> {
        let inode = Self::iget(sb, 1)?;
        dentry::Root::try_new(inode)
    }

    fn read_xattr(
        _: &DEntry<Self>,
        inode: &INode<Self>,
        name: &CStr,
        outbuf: &mut [u8],
    ) -> Result<usize> {
        if inode.data().flags & inode_flags::OPAQUE == 0
            || name.as_bytes() != b"trusted.overlay.opaque"
        {
            return Err(ENODATA);
        }

        if !outbuf.is_empty() {
            outbuf[0] = b'y';
        }

        Ok(1)
    }

    fn statfs(dentry: &DEntry<Self>) -> Result<Stat> {
        let data = dentry.super_block().data();
        Ok(Stat {
            magic: TARFS_MAGIC,
            namelen: i64::MAX,
            bsize: TARFS_BSIZE as _,
            blocks: data.inode_table_offset / TARFS_BSIZE,
            files: data.inode_count,
        })
    }
}

impl iomap::Operations for TarFs {
    type FileSystem = Self;

    fn begin<'a>(
        inode: &'a INode<Self>,
        pos: Offset,
        length: Offset,
        _flags: u32,
        map: &mut iomap::Map<'a>,
        _srcmap: &mut iomap::Map<'a>,
    ) -> Result {
        // TODO: Handle this better.
        let size = inode.size();
        map.set_offset(pos)
            .set_length(length.try_into()?)
            .set_flags(iomap::map_flags::MERGED)
            .set_bdev(Some(inode.super_block().bdev()));

        if pos >= size {
            map.set_type(iomap::Type::Hole);
            return Ok(());
        }

        if size - pos < length {
            // TODO: Avoid conversion?
            map.set_length((size - pos).try_into()?);
        }

        map.set_type(iomap::Type::Mapped)
            .set_addr(u64::try_from(pos)? + inode.data().offset);
        Ok(())
    }
}

#[vtable]
impl inode::Operations for TarFs {
    type FileSystem = Self;

    fn lookup(
        parent: &INode<Self>,
        dentry: dentry::Unhashed<'_, Self>,
    ) -> Result<Option<ARef<DEntry<Self>>>> {
        let name = dentry.name();
        let name_len = u64::try_from(name.len())?;
        let sb = parent.super_block();

        for v in sb.read(parent.data().offset, parent.size().try_into()?)? {
            for e in DirEntry::from_bytes_to_slice(v?.data()).ok_or(EIO)? {
                if e.name_len.value() != name_len || e.name_len.value() > usize::MAX as u64 {
                    continue;
                }
                if Self::name_eq(sb, name, e.name_offset.value())? {
                    return match Self::iget(sb, e.ino.value()) {
                        Ok(inode) => dentry.splice_alias(Some(inode)),
                        Err(e) => {
                            if e == ENOENT {
                                dentry.splice_alias(None)
                            } else {
                                Err(e)
                            }
                        }
                    };
                }
            }
        }

        dentry.splice_alias(None)
    }
}

#[vtable]
impl file::Operations for TarFs {
    type FileSystem = Self;

    fn seek(file: &File<Self>, offset: Offset, whence: file::Whence) -> Result<Offset> {
        file::generic_seek(file, offset, whence)
    }

    fn read(_: &File<Self>, _: &mut user::Writer, _: &mut Offset) -> Result<usize> {
        Err(EISDIR)
    }

    fn read_dir(file: &File<Self>, emitter: &mut file::DirEmitter) -> Result {
        let inode = file.inode();
        let sb = inode.super_block();
        let mut name = Vec::<u8>::new();
        let pos = emitter.pos();

        if pos < 0 || pos % size_of::<DirEntry>() as i64 != 0 {
            return Err(ENOENT);
        }

        if pos >= inode.size() {
            return Ok(());
        }

        // Make sure the inode data doesn't overflow the data area.
        let size = u64::try_from(inode.size())?;
        if inode.data().offset.checked_add(size).ok_or(EIO)? > sb.data().data_size {
            return Err(EIO);
        }

        for v in sb.read(inode.data().offset + pos as u64, size - pos as u64)? {
            for e in DirEntry::from_bytes_to_slice(v?.data()).ok_or(EIO)? {
                let name_len = usize::try_from(e.name_len.value())?;
                if name_len > name.len() {
                    name.try_resize(name_len, 0)?;
                }

                Self::read_name(sb, &mut name[..name_len], e.name_offset.value())?;

                if !emitter.emit(
                    size_of::<DirEntry>() as i64,
                    &name[..name_len],
                    e.ino.value(),
                    file::DirEntryType::try_from(u32::from(e.etype))?,
                ) {
                    return Ok(());
                }
            }
        }

        Ok(())
    }
}
