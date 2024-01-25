// SPDX-License-Identifier: GPL-2.0

//! Ext2 file system.

use alloc::vec::Vec;
use core::mem::size_of;
use defs::*;
use kernel::fs::{
    self, address_space, dentry, dentry::DEntry, file, file::File, inode, inode::INode, iomap, sb,
    sb::SuperBlock, Offset,
};
use kernel::types::{ARef, Either, FromBytes, Locked, LE};
use kernel::{block, c_str, prelude::*, str::CString, time::Timespec, user, PAGE_SIZE};

pub mod defs;

kernel::module_fs! {
    type: Ext2Fs,
    name: "ext2",
    author: "Wedson Almeida Filho <walmeida@microsoft.com>",
    description: "ext2 file system",
    license: "GPL",
}

const SB_OFFSET: Offset = 1024;

struct INodeData {
    data_blocks: [u32; defs::EXT2_N_BLOCKS],
}

struct Ext2Fs {
    mapper: inode::Mapper,
    block_size: u32,
    has_file_type: bool,
    _block_size_bits: u32,
    inodes_per_block: u32,
    inodes_per_group: u32,
    inode_count: u32,
    inode_size: u16,
    first_ino: u32,
    group: Vec<defs::Group>,
}

impl Ext2Fs {
    fn iget(sb: &SuperBlock<Self>, ino: u32) -> Result<ARef<INode<Self>>> {
        let s = sb.data();
        if (ino != EXT2_ROOT_INO && ino < s.first_ino) || ino > s.inode_count {
            return Err(ENOENT);
        }
        let group = ((ino - 1) / s.inodes_per_group) as usize;
        let offset = (ino - 1) % s.inodes_per_group;

        if group >= s.group.len() {
            return Err(ENOENT);
        }

        // Create an inode or find an existing (cached) one.
        let mut inode = match sb.get_or_create_inode(ino.into())? {
            Either::Left(existing) => return Ok(existing),
            Either::Right(new) => new,
        };

        let inodes_block = Offset::from(s.group[group].inode_table.value());
        let inode_block = inodes_block + Offset::from(offset / s.inodes_per_block);
        let offset = (offset % s.inodes_per_block) as usize;
        let b = sb
            .data()
            .mapper
            .mapped_folio(inode_block * Offset::from(s.block_size))?;
        let idata = defs::INode::from_bytes(&b, offset * s.inode_size as usize).ok_or(EIO)?;
        let mode = idata.mode.value();

        if idata.links_count.value() == 0 && (mode == 0 || idata.dtime.value() != 0) {
            return Err(ESTALE);
        }

        const DIR_FOPS: file::Ops<Ext2Fs> = file::Ops::new::<Ext2Fs>();
        const DIR_IOPS: inode::Ops<Ext2Fs> = inode::Ops::new::<Ext2Fs>();
        const FILE_AOPS: address_space::Ops<Ext2Fs> = iomap::ro_aops::<Ext2Fs>();

        let mut size = idata.size.value().into();
        let typ = match mode & fs::mode::S_IFMT {
            fs::mode::S_IFREG => {
                size |= Offset::from(idata.dir_acl.value())
                    .checked_shl(32)
                    .ok_or(EUCLEAN)?;
                inode
                    .set_aops(FILE_AOPS)
                    .set_fops(file::Ops::generic_ro_file());
                inode::Type::Reg
            }
            fs::mode::S_IFDIR => {
                inode
                    .set_iops(DIR_IOPS)
                    .set_fops(DIR_FOPS)
                    .set_aops(FILE_AOPS);
                inode::Type::Dir
            }
            fs::mode::S_IFLNK => {
                if idata.blocks.value() == 0 {
                    const OFFSET: usize = core::mem::offset_of!(defs::INode, block);
                    let name = &b[offset * usize::from(s.inode_size) + OFFSET..];
                    let name_len = size as usize;
                    if name_len > name.len() || name_len == 0 {
                        return Err(EIO);
                    }
                    inode.set_iops(inode::Ops::simple_symlink_inode());
                    inode::Type::Lnk(Some(CString::try_from(&name[..name_len])?))
                } else {
                    inode
                        .set_aops(FILE_AOPS)
                        .set_iops(inode::Ops::page_symlink_inode());
                    inode::Type::Lnk(None)
                }
            }
            fs::mode::S_IFSOCK => inode::Type::Sock,
            fs::mode::S_IFIFO => inode::Type::Fifo,
            fs::mode::S_IFCHR => {
                let (major, minor) = decode_dev(&idata.block);
                inode::Type::Chr(major, minor)
            }
            fs::mode::S_IFBLK => {
                let (major, minor) = decode_dev(&idata.block);
                inode::Type::Blk(major, minor)
            }
            _ => return Err(ENOENT),
        };
        inode.init(inode::Params {
            typ,
            mode: mode & 0o777,
            size,
            blocks: idata.blocks.value().into(),
            nlink: idata.links_count.value().into(),
            uid: u32::from(idata.uid.value()) | u32::from(idata.uid_high.value()) << 16,
            gid: u32::from(idata.gid.value()) | u32::from(idata.gid_high.value()) << 16,
            ctime: Timespec::new(idata.ctime.value().into(), 0)?,
            mtime: Timespec::new(idata.mtime.value().into(), 0)?,
            atime: Timespec::new(idata.atime.value().into(), 0)?,
            value: INodeData {
                data_blocks: core::array::from_fn(|i| idata.block[i].value()),
            },
        })
    }

    fn offsets<'a>(&self, mut block: u64, out: &'a mut [u32]) -> Option<&'a [u32]> {
        let ptrs = u64::from(self.block_size / size_of::<u32>() as u32);
        let ptr_mask = ptrs - 1;
        let ptr_bits = ptrs.trailing_zeros();

        if block < EXT2_NDIR_BLOCKS as u64 {
            out[0] = block as u32;
            return Some(&out[..1]);
        }

        block -= EXT2_NDIR_BLOCKS as u64;
        if block < ptrs {
            out[0] = EXT2_IND_BLOCK as u32;
            out[1] = block as u32;
            return Some(&out[..2]);
        }

        block -= ptrs;
        if block < (1 << (2 * ptr_bits)) {
            out[0] = EXT2_DIND_BLOCK as u32;
            out[1] = (block >> ptr_bits) as u32;
            out[2] = (block & ptr_mask) as u32;
            return Some(&out[..3]);
        }

        block -= ptrs * ptrs;
        if block < ptrs * ptrs * ptrs {
            out[0] = EXT2_TIND_BLOCK as u32;
            out[1] = (block >> (2 * ptr_bits)) as u32;
            out[2] = ((block >> ptr_bits) & ptr_mask) as u32;
            out[3] = (block & ptr_mask) as u32;
            return Some(&out[..4]);
        }

        None
    }

    fn offset_to_block(inode: &INode<Self>, block: Offset) -> Result<u64> {
        let s = inode.super_block().data();
        let mut indices = [0u32; 4];
        let boffsets = s.offsets(block as u64, &mut indices).ok_or(EIO)?;
        let mut boffset = inode.data().data_blocks[boffsets[0] as usize];
        let mapper = &s.mapper;
        for i in &boffsets[1..] {
            let b = mapper.mapped_folio(Offset::from(boffset) * Offset::from(s.block_size))?;
            let table = LE::<u32>::from_bytes_to_slice(&b).ok_or(EIO)?;
            boffset = table[*i as usize].value();
        }
        Ok(boffset.into())
    }

    fn check_descriptors(s: &Super, groups: &[Group]) -> Result {
        for (i, g) in groups.iter().enumerate() {
            let first = i as u32 * s.blocks_per_group.value() + s.first_data_block.value();
            let last = if i == groups.len() - 1 {
                s.blocks_count.value()
            } else {
                first + s.blocks_per_group.value() - 1
            };

            if g.block_bitmap.value() < first || g.block_bitmap.value() > last {
                pr_err!(
                    "Block bitmap for group {i} no in group (block {})\n",
                    g.block_bitmap.value()
                );
                return Err(EINVAL);
            }

            if g.inode_bitmap.value() < first || g.inode_bitmap.value() > last {
                pr_err!(
                    "Inode bitmap for group {i} no in group (block {})\n",
                    g.inode_bitmap.value()
                );
                return Err(EINVAL);
            }

            if g.inode_table.value() < first || g.inode_table.value() > last {
                pr_err!(
                    "Inode table for group {i} no in group (block {})\n",
                    g.inode_table.value()
                );
                return Err(EINVAL);
            }
        }
        Ok(())
    }
}

impl fs::FileSystem for Ext2Fs {
    type Data = Box<Self>;
    type INodeData = INodeData;
    const NAME: &'static CStr = c_str!("rust-ext2");
    const SUPER_TYPE: sb::Type = sb::Type::BlockDev;

    fn fill_super(
        sb: &mut SuperBlock<Self, sb::New>,
        mapper: Option<inode::Mapper>,
    ) -> Result<Self::Data> {
        let Some(mapper) = mapper else {
            return Err(EINVAL);
        };

        if sb.min_blocksize(PAGE_SIZE as i32) == 0 {
            pr_err!("Unable to set block size\n");
            return Err(EINVAL);
        }

        // Map the super block and check the magic number.
        let mapped = mapper.mapped_folio(SB_OFFSET)?;
        let s = Super::from_bytes(&mapped, 0).ok_or(EIO)?;

        if s.magic.value() != EXT2_SUPER_MAGIC {
            return Err(EINVAL);
        }

        // Check for unsupported flags.
        let mut has_file_type = false;
        if s.rev_level.value() >= EXT2_DYNAMIC_REV {
            let features = s.feature_incompat.value();
            if features & !EXT2_FEATURE_INCOMPAT_FILETYPE != 0 {
                pr_err!("Unsupported incompatible feature: {:x}\n", features);
                return Err(EINVAL);
            }

            has_file_type = features & EXT2_FEATURE_INCOMPAT_FILETYPE != 0;

            let features = s.feature_ro_compat.value();
            if !sb.rdonly() && features != 0 {
                pr_err!("Unsupported rw incompatible feature: {:x}\n", features);
                return Err(EINVAL);
            }
        }

        // Set the block size.
        let block_size_bits = s.log_block_size.value();
        if block_size_bits > EXT2_MAX_BLOCK_LOG_SIZE - 10 {
            pr_err!("Invalid log block size: {}\n", block_size_bits);
            return Err(EINVAL);
        }

        let block_size = 1024u32 << block_size_bits;
        if sb.min_blocksize(block_size as i32) != block_size as i32 {
            pr_err!("Bad block size: {}\n", block_size);
            return Err(ENXIO);
        }

        // Get the first inode and the inode size.
        let (inode_size, first_ino) = if s.rev_level.value() == EXT2_GOOD_OLD_REV {
            (EXT2_GOOD_OLD_INODE_SIZE, EXT2_GOOD_OLD_FIRST_INO)
        } else {
            let size = s.inode_size.value();
            if size < EXT2_GOOD_OLD_INODE_SIZE
                || !size.is_power_of_two()
                || u32::from(size) > block_size
            {
                pr_err!("Unsupported inode size: {}\n", size);
                return Err(EINVAL);
            }
            (size, s.first_ino.value())
        };

        // Get the number of inodes per group and per block.
        let inode_count = s.inodes_count.value();
        let inodes_per_group = s.inodes_per_group.value();
        let inodes_per_block = block_size / u32::from(inode_size);
        if inodes_per_group == 0 || inodes_per_block == 0 {
            return Err(EINVAL);
        }

        if inodes_per_group > block_size * 8 || inodes_per_group < inodes_per_block {
            pr_err!("Bad inodes per group: {}\n", inodes_per_group);
            return Err(EINVAL);
        }

        // Check the size of the groups.
        let itb_per_group = inodes_per_group / inodes_per_block;
        let blocks_per_group = s.blocks_per_group.value();
        if blocks_per_group > block_size * 8 || blocks_per_group <= itb_per_group + 3 {
            pr_err!("Bad blocks per group: {}\n", blocks_per_group);
            return Err(EINVAL);
        }

        let blocks_count = s.blocks_count.value();
        if block::Sector::from(blocks_count) > sb.sector_count() >> (1 + block_size_bits) {
            pr_err!(
                "Block count ({blocks_count}) exceeds size of device ({})\n",
                sb.sector_count() >> (1 + block_size_bits)
            );
            return Err(EINVAL);
        }

        let group_count = (blocks_count - s.first_data_block.value() - 1) / blocks_per_group + 1;
        if group_count * inodes_per_group != inode_count {
            pr_err!(
                "Unexpected inode count: {inode_count} vs {}",
                group_count * inodes_per_group
            );
            return Err(EINVAL);
        }

        let mut groups = Vec::new();
        groups.reserve(group_count as usize, GFP_NOFS)?;

        let mut remain = group_count;
        let mut offset = (SB_OFFSET / Offset::from(block_size) + 1) * Offset::from(block_size);
        while remain > 0 {
            let b = mapper.mapped_folio(offset)?;
            for g in Group::from_bytes_to_slice(&b).ok_or(EIO)? {
                groups.push(*g, GFP_NOFS)?;
                remain -= 1;
                if remain == 0 {
                    break;
                }
            }
            offset += Offset::try_from(b.len())?;
        }

        Self::check_descriptors(s, &groups)?;

        sb.set_magic(s.magic.value().into());
        drop(mapped);
        Ok(Box::new(
            Ext2Fs {
                mapper,
                block_size,
                _block_size_bits: block_size_bits,
                has_file_type,
                inodes_per_group,
                inodes_per_block,
                inode_count,
                inode_size,
                first_ino,
                group: groups,
            },
            GFP_KERNEL,
        )?)
    }

    fn init_root(sb: &SuperBlock<Self>) -> Result<dentry::Root<Self>> {
        let inode = Self::iget(sb, EXT2_ROOT_INO)?;
        dentry::Root::try_new(inode)
    }
}

fn rec_len(d: &DirEntry) -> u32 {
    let len = d.rec_len.value();

    if PAGE_SIZE >= 65536 && len == u16::MAX {
        1u32 << 16
    } else {
        len.into()
    }
}

#[vtable]
impl file::Operations for Ext2Fs {
    type FileSystem = Self;

    fn seek(file: &File<Self>, offset: Offset, whence: file::Whence) -> Result<Offset> {
        file::generic_seek(file, offset, whence)
    }

    fn read(_: &File<Self>, _: &mut user::Writer, _: &mut Offset) -> Result<usize> {
        Err(EISDIR)
    }

    fn read_dir(
        _file: &File<Self>,
        inode: &Locked<&INode<Self>, inode::ReadSem>,
        emitter: &mut file::DirEmitter,
    ) -> Result {
        let has_file_type = inode.super_block().data().has_file_type;

        inode.for_each_page(emitter.pos(), Offset::MAX, |data| {
            let mut offset = 0usize;
            let mut acc: Offset = 0;
            let limit = data.len().saturating_sub(size_of::<DirEntry>());
            while offset < limit {
                let dirent = DirEntry::from_bytes(data, offset).ok_or(EIO)?;
                offset += size_of::<DirEntry>();

                let name_len = usize::from(dirent.name_len);
                if data.len() - offset < name_len {
                    return Err(EIO);
                }

                let name = &data[offset..][..name_len];
                let rec_len = rec_len(dirent);
                offset = offset - size_of::<DirEntry>() + rec_len as usize;
                if rec_len == 0 || offset > data.len() {
                    return Err(EIO);
                }

                acc += Offset::from(rec_len);
                let ino = dirent.inode.value();
                if ino == 0 {
                    continue;
                }

                let t = if !has_file_type {
                    file::DirEntryType::Unknown
                } else {
                    match dirent.file_type {
                        FT_REG_FILE => file::DirEntryType::Reg,
                        FT_DIR => file::DirEntryType::Dir,
                        FT_SYMLINK => file::DirEntryType::Lnk,
                        FT_CHRDEV => file::DirEntryType::Chr,
                        FT_BLKDEV => file::DirEntryType::Blk,
                        FT_FIFO => file::DirEntryType::Fifo,
                        FT_SOCK => file::DirEntryType::Sock,
                        _ => continue,
                    }
                };

                if !emitter.emit(acc, name, ino.into(), t) {
                    return Ok(Some(()));
                }
                acc = 0;
            }
            Ok(None)
        })?;
        Ok(())
    }
}

#[vtable]
impl inode::Operations for Ext2Fs {
    type FileSystem = Self;

    fn lookup(
        parent: &Locked<&INode<Self>, inode::ReadSem>,
        dentry: dentry::Unhashed<'_, Self>,
    ) -> Result<Option<ARef<DEntry<Self>>>> {
        let inode = parent.for_each_page(0, Offset::MAX, |data| {
            let mut offset = 0usize;
            while data.len() - offset > size_of::<DirEntry>() {
                let dirent = DirEntry::from_bytes(data, offset).ok_or(EIO)?;
                offset += size_of::<DirEntry>();

                let name_len = usize::from(dirent.name_len);
                if data.len() - offset < name_len {
                    return Err(EIO);
                }

                let name = &data[offset..][..name_len];

                offset = offset - size_of::<DirEntry>() + usize::from(dirent.rec_len.value());
                if offset > data.len() {
                    return Err(EIO);
                }

                let ino = dirent.inode.value();
                if ino != 0 && name == dentry.name() {
                    return Ok(Some(Self::iget(parent.super_block(), ino)?));
                }
            }
            Ok(None)
        })?;

        dentry.splice_alias(inode)
    }
}

impl iomap::Operations for Ext2Fs {
    type FileSystem = Self;

    fn begin<'a>(
        inode: &'a INode<Self>,
        pos: Offset,
        length: Offset,
        _flags: u32,
        map: &mut iomap::Map<'a>,
        _srcmap: &mut iomap::Map<'a>,
    ) -> Result {
        let size = inode.size();
        if pos >= size {
            map.set_offset(pos)
                .set_length(length.try_into()?)
                .set_flags(iomap::map_flags::MERGED)
                .set_type(iomap::Type::Hole);
            return Ok(());
        }

        let block_size = inode.super_block().data().block_size as Offset;
        let block = pos / block_size;

        let boffset = Self::offset_to_block(inode, block)?;
        map.set_offset(block * block_size)
            .set_length(block_size as u64)
            .set_flags(iomap::map_flags::MERGED)
            .set_type(iomap::Type::Mapped)
            .set_bdev(Some(inode.super_block().bdev()))
            .set_addr(boffset * block_size as u64);

        Ok(())
    }
}

fn decode_dev(block: &[LE<u32>]) -> (u32, u32) {
    let v = block[0].value();
    if v != 0 {
        ((v >> 8) & 255, v & 255)
    } else {
        let v = block[1].value();
        ((v & 0xfff00) >> 8, (v & 0xff) | ((v >> 12) & 0xfff00))
    }
}
