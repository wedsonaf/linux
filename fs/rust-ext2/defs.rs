// SPDX-License-Identifier: GPL-2.0

//! Definitions of tarfs structures.

use kernel::types::LE;

pub(crate) const EXT2_SUPER_MAGIC: u16 = 0xEF53;

pub(crate) const EXT2_MAX_BLOCK_LOG_SIZE: u32 = 16;

pub(crate) const EXT2_GOOD_OLD_REV: u32 = 0; /* The good old (original) format */
pub(crate) const EXT2_DYNAMIC_REV: u32 = 1; /* V2 format w/ dynamic inode sizes */

pub(crate) const EXT2_GOOD_OLD_INODE_SIZE: u16 = 128;

pub(crate) const EXT2_ROOT_INO: u32 = 2; /* Root inode */

/* First non-reserved inode for old ext2 filesystems. */
pub(crate) const EXT2_GOOD_OLD_FIRST_INO: u32 = 11;

pub(crate) const EXT2_FEATURE_INCOMPAT_FILETYPE: u32 = 0x0002;

/*
 * Constants relative to the data blocks
 */
pub(crate) const EXT2_NDIR_BLOCKS: usize = 12;
pub(crate) const EXT2_IND_BLOCK: usize = EXT2_NDIR_BLOCKS;
pub(crate) const EXT2_DIND_BLOCK: usize = EXT2_IND_BLOCK + 1;
pub(crate) const EXT2_TIND_BLOCK: usize = EXT2_DIND_BLOCK + 1;
pub(crate) const EXT2_N_BLOCKS: usize = EXT2_TIND_BLOCK + 1;

kernel::derive_readable_from_bytes! {
    #[repr(C)]
    pub(crate) struct Super {
        pub(crate) inodes_count: LE<u32>,
        pub(crate) blocks_count: LE<u32>,
        pub(crate) r_blocks_count: LE<u32>,
        pub(crate) free_blocks_count: LE<u32>, /* Free blocks count */
        pub(crate) free_inodes_count: LE<u32>, /* Free inodes count */
        pub(crate) first_data_block: LE<u32>,  /* First Data Block */
        pub(crate) log_block_size: LE<u32>,    /* Block size */
        pub(crate) log_frag_size: LE<u32>,     /* Fragment size */
        pub(crate) blocks_per_group: LE<u32>,  /* # Blocks per group */
        pub(crate) frags_per_group: LE<u32>,   /* # Fragments per group */
        pub(crate) inodes_per_group: LE<u32>,  /* # Inodes per group */
        pub(crate) mtime: LE<u32>,             /* Mount time */
        pub(crate) wtime: LE<u32>,             /* Write time */
        pub(crate) mnt_count: LE<u16>,         /* Mount count */
        pub(crate) max_mnt_count: LE<u16>,     /* Maximal mount count */
        pub(crate) magic: LE<u16>,             /* Magic signature */
        pub(crate) state: LE<u16>,             /* File system state */
        pub(crate) errors: LE<u16>,            /* Behaviour when detecting errors */
        pub(crate) minor_rev_level: LE<u16>,   /* minor revision level */
        pub(crate) lastcheck: LE<u32>,         /* time of last check */
        pub(crate) checkinterval: LE<u32>,     /* max. time between checks */
        pub(crate) creator_os: LE<u32>,        /* OS */
        pub(crate) rev_level: LE<u32>,         /* Revision level */
        pub(crate) def_resuid: LE<u16>,        /* Default uid for reserved blocks */
        pub(crate) def_resgid: LE<u16>,        /* Default gid for reserved blocks */
        /*
         * These fields are for EXT2_DYNAMIC_REV superblocks only.
         *
         * Note: the difference between the compatible feature set and
         * the incompatible feature set is that if there is a bit set
         * in the incompatible feature set that the kernel doesn't
         * know about, it should refuse to mount the filesystem.
         *
         * e2fsck's requirements are more strict; if it doesn't know
         * about a feature in either the compatible or incompatible
         * feature set, it must abort and not try to meddle with
         * things it doesn't understand...
         */
        pub(crate) first_ino: LE<u32>,              /* First non-reserved inode */
        pub(crate) inode_size: LE<u16>,             /* size of inode structure */
        pub(crate) block_group_nr: LE<u16>,         /* block group # of this superblock */
        pub(crate) feature_compat: LE<u32>,         /* compatible feature set */
        pub(crate) feature_incompat: LE<u32>,       /* incompatible feature set */
        pub(crate) feature_ro_compat: LE<u32>,      /* readonly-compatible feature set */
        pub(crate) uuid: [u8; 16],                  /* 128-bit uuid for volume */
        pub(crate) volume_name: [u8; 16],           /* volume name */
        pub(crate) last_mounted: [u8; 64],          /* directory where last mounted */
        pub(crate) algorithm_usage_bitmap: LE<u32>, /* For compression */
        /*
         * Performance hints.  Directory preallocation should only
         * happen if the EXT2_COMPAT_PREALLOC flag is on.
         */
        pub(crate) prealloc_blocks: u8,    /* Nr of blocks to try to preallocate*/
        pub(crate) prealloc_dir_blocks: u8,        /* Nr to preallocate for dirs */
        padding1: u16,
        /*
         * Journaling support valid if EXT3_FEATURE_COMPAT_HAS_JOURNAL set.
         */
        pub(crate) journal_uuid: [u8; 16],      /* uuid of journal superblock */
        pub(crate) journal_inum: u32,           /* inode number of journal file */
        pub(crate) journal_dev: u32,            /* device number of journal file */
        pub(crate) last_orphan: u32,            /* start of list of inodes to delete */
        pub(crate) hash_seed: [u32; 4],         /* HTREE hash seed */
        pub(crate) def_hash_version: u8,        /* Default hash version to use */
        pub(crate) reserved_char_pad: u8,
        pub(crate) reserved_word_pad: u16,
        pub(crate) default_mount_opts: LE<u32>,
        pub(crate) first_meta_bg: LE<u32>,      /* First metablock block group */
        reserved: [u32; 190],                   /* Padding to the end of the block */
    }

    #[repr(C)]
    #[derive(Clone, Copy)]
    pub(crate) struct Group {
        /// Blocks bitmap block.
        pub block_bitmap: LE<u32>,

        /// Inodes bitmap block.
        pub inode_bitmap: LE<u32>,

        /// Inodes table block.
        pub inode_table: LE<u32>,

        /// Number of free blocks.
        pub free_blocks_count: LE<u16>,

        /// Number of free inodes.
        pub free_inodes_count: LE<u16>,

        /// Number of directories.
        pub used_dirs_count: LE<u16>,

        pad: LE<u16>,
        reserved: [u32; 3],
    }

    #[repr(C)]
    pub(crate) struct INode {
        pub mode: LE<u16>,                  /* File mode */
        pub uid: LE<u16>,                   /* Low 16 bits of Owner Uid */
        pub size: LE<u32>,                  /* Size in bytes */
        pub atime: LE<u32>,                 /* Access time */
        pub ctime: LE<u32>,                 /* Creation time */
        pub mtime: LE<u32>,                 /* Modification time */
        pub dtime: LE<u32>,                 /* Deletion Time */
        pub gid: LE<u16>,                   /* Low 16 bits of Group Id */
        pub links_count: LE<u16>,           /* Links count */
        pub blocks: LE<u32>,                /* Blocks count */
        pub flags: LE<u32>,                 /* File flags */
        pub reserved1: LE<u32>,
        pub block: [LE<u32>; EXT2_N_BLOCKS],/* Pointers to blocks */
        pub generation: LE<u32>,            /* File version (for NFS) */
        pub file_acl: LE<u32>,              /* File ACL */
        pub dir_acl: LE<u32>,               /* Directory ACL */
        pub faddr: LE<u32>,                 /* Fragment address */
        pub frag: u8,	                    /* Fragment number */
        pub fsize: u8,	                    /* Fragment size */
        pub pad1: LE<u16>,
        pub uid_high: LE<u16>,
        pub gid_high: LE<u16>,
        pub reserved2: LE<u32>,
    }

    #[repr(C)]
    pub(crate) struct DirEntry {
        pub(crate) inode: LE<u32>,       /* Inode number */
        pub(crate) rec_len: LE<u16>,     /* Directory entry length */
        pub(crate) name_len: u8,         /* Name length */
        pub(crate) file_type: u8,        /* Only if the "filetype" feature flag is set. */
    }
}

pub(crate) const FT_REG_FILE: u8 = 1;
pub(crate) const FT_DIR: u8 = 2;
pub(crate) const FT_CHRDEV: u8 = 3;
pub(crate) const FT_BLKDEV: u8 = 4;
pub(crate) const FT_FIFO: u8 = 5;
pub(crate) const FT_SOCK: u8 = 6;
pub(crate) const FT_SYMLINK: u8 = 7;
