// SPDX-License-Identifier: GPL-2.0

//! Implementation of 9P server that exposes the local filesystem.

use super::{buffer::BufferWriter, protocol::*, reserve};
use kernel::{
    file::{self, File},
    fs,
    prelude::*,
    rbtree::RBTree,
    sync::smutex::Mutex,
    ARef,
};

struct ServerInner {
    id_table: RBTree<u32, IdData>,
}

pub(crate) struct Server {
    root: ARef<File>,
    inner: Mutex<ServerInner>,
}

impl Server {
    pub(crate) fn new(root: ARef<File>) -> Self {
        Self {
            root,
            inner: Mutex::new(ServerInner {
                id_table: RBTree::new(),
            }),
        }
    }

    pub(crate) fn initial_version(outbuf: &mut [u8], v: &Version<'_>) -> Result<usize> {
        // TODO: Validate that the value of `msize` makes sense.
        const VERSION: &str = "9P2000.L";
        if v.ver != VERSION {
            return Err(EOPNOTSUPP);
        }

        v.reply(outbuf, v.msize, VERSION)
    }

    fn version(&self, outbuf: &mut [u8], v: &Version<'_>) -> Result<usize> {
        let len = Self::initial_version(outbuf, v)?;

        // Clunk all fids.
        self.inner.lock().id_table = RBTree::new();

        // TODO: Cancel all pending requests.
        Ok(len)
    }

    fn attach(&self, outbuf: &mut [u8], a: &Attach<'_>) -> Result<usize> {
        let path = self.root.path().clone();
        let len = a.reply(outbuf, &qid(path.dentry().inode().unwrap()))?;
        let node = RBTree::try_allocate_node(a.fid, IdData::new(path))?;

        let mut guard = self.inner.lock();

        // Don't allow attaching to an existing fid.
        if guard.id_table.get(&a.fid).is_some() {
            return Err(EBUSY);
        }

        guard.id_table.insert(node);

        Ok(len)
    }

    fn clunk(&self, outbuf: &mut [u8], c: &Clunk) -> Result<usize> {
        self.inner
            .lock()
            .id_table
            .remove_node(&c.fid)
            .ok_or(EBADF)?;
        c.reply(outbuf)
    }

    fn open(&self, outbuf: &mut [u8], o: &Open) -> Result<usize> {
        use file::flags::*;
        const ALLOWED_FLAGS: u32 = O_APPEND
            | O_DIRECTORY
            | O_LARGEFILE
            | O_NOATIME
            | O_NOCTTY
            | O_NOFOLLOW
            | O_TMPFILE
            | O_TRUNC
            | O_ACCMODE;

        // Get the path to open.
        let path = {
            let guard = self.inner.lock();
            let data = guard.id_table.get(&o.fid).ok_or(EBADF)?;
            if data.file.is_some() {
                return Err(EALREADY);
            }

            data.path.clone()
        };

        // Actually open the path.
        let file = path.open(o.flags & ALLOWED_FLAGS, self.root.cred())?;

        // Try to store the file into the table again. We need to recheck the state of the
        // descriptor table.
        {
            let mut guard = self.inner.lock();
            let data = guard.id_table.get_mut(&o.fid).ok_or(EBADF)?;
            if data.file.is_some() {
                return Err(EALREADY);
            }

            // Check if the id wasn't clunked and walked to a different path.
            if path != data.path {
                return Err(EINVAL);
            }

            data.file = Some(file.clone());
        }

        // TODO: Figure out what to return for iounit.
        // From man page: The iounit field returned by open and create may be zero. If it is not,
        // it is the maximum number of bytes that are guaranteed to be read from or written to the
        // file without breaking the I/O transfer into multiple 9P messages; see read(5).
        o.reply(outbuf, &qid(file.inode()), 0u32)
    }

    fn readdir(&self, outbuf: &mut [u8], r: &ReadDir) -> Result<usize> {
        let file = {
            let guard = self.inner.lock();
            let data = guard.id_table.get(&r.fid).ok_or(EBADF)?;
            data.file.as_ref().ok_or(EINVAL)?.clone()
        };

        if file.inode().kind() != fs::inode_kind::DIR {
            return Err(EINVAL);
        }

        let mut b = r.reply(outbuf, r.size as usize)?;

        file.readdir(r.offset, |cbname, i, ino, typ| {
            use file::dirent::*;
            use fs::lookup::*;

            // Skip anything that isn't a regular file, directory or symlink.
            if i < r.offset || (typ != DT_REG && typ != DT_LNK && typ != DT_DIR) {
                return Ok(true);
            }

            // Just continue enumeration if conversion to string fails.
            let uname = match core::str::from_utf8(cbname) {
                Err(_) => return Ok(true),
                Ok(n) => n,
            };

            if uname == "." || uname == ".." {
                return Ok(true);
            }

            // Ensure that we don't cross devices. We can remove this if decide to support it.
            let newpath = file.path().lookup(uname.as_bytes(), LOOKUP_BENEATH)?;
            if !newpath.is_same_mnt(file.path()) {
                return Ok(true);
            }

            // We continue the enumeration as long as we manage to write to the response.
            let x = b
                .write(&dirent(uname.as_bytes(), ino, i + 1, typ as _))
                .is_ok();
            Ok(x)
        })?;
        Ok(b.finish())
    }

    fn get_attr(&self, outbuf: &mut [u8], a: &GetAttr) -> Result<usize> {
        let guard = self.inner.lock();
        let data = guard.id_table.get(&a.fid).ok_or(EBADF)?;
        // TODO: If `attrs` needs to do anything expensive, we need to change this to release the
        // lock.
        a.reply(
            outbuf,
            &attrs(data.path.dentry().inode().unwrap(), a.request_mask),
        )
    }

    fn readlink(&self, outbuf: &mut [u8], r: &ReadLink) -> Result<usize> {
        let dentry = {
            let guard = self.inner.lock();
            let data = guard.id_table.get(&r.fid).ok_or(EBADF)?;
            ARef::<_>::from(data.path.dentry())
        };

        let inode = dentry.inode().ok_or(EINVAL)?;
        if inode.kind() != fs::inode_kind::LNK {
            return Err(EINVAL);
        }
        let target = dentry.get_link()?;
        r.reply(outbuf, &target)
    }

    fn read(&self, outbuf: &mut [u8], r: &Read) -> Result<usize> {
        let file = {
            let guard = self.inner.lock();
            let data = guard.id_table.get(&r.fid).ok_or(EBADF)?;
            data.file.as_ref().ok_or(EINVAL)?.clone()
        };

        if file.inode().kind() != fs::inode_kind::REG {
            return Err(EINVAL);
        }

        let mut b = r.reply(outbuf, r.size as usize)?;
        if r.size == 0 {
            return Ok(b.finish());
        }

        let buf = b.buffer();
        let to_copy = core::cmp::min(r.size as usize, buf.len());
        let read = file.read(&mut buf[..to_copy], r.offset)?;
        b.write(&reserve(read as usize))?;
        Ok(b.finish())
    }

    fn walk_next(b: &mut BufferWriter<'_>, path: &fs::Path, name: &str) -> Result<fs::Path> {
        use fs::lookup::*;
        let name = kernel::str::CString::try_from_fmt(fmt!("{name}"))?;
        let newpath = path.lookup(&name, LOOKUP_BENEATH)?;
        if !newpath.is_same_mnt(path) {
            return Err(ENOENT);
        }

        let inode = newpath.dentry().inode().ok_or(EINVAL)?;
        match inode.kind() {
            fs::inode_kind::LNK | fs::inode_kind::REG | fs::inode_kind::DIR => {}
            _ => return Err(ENOENT),
        }
        b.write(&qid(inode))?;
        Ok(newpath)
    }

    fn walk(&self, outbuf: &mut [u8], w: &Walk<'_>) -> Result<usize> {
        let initial_path = {
            let guard = self.inner.lock();

            // Find the initial entry.
            let data = guard.id_table.get(&w.fid).ok_or(EBADF)?;

            // Don't allow reassigning an existing fid (except the one we're using).
            if w.new_fid != w.fid && guard.id_table.get(&w.new_fid).is_some() {
                return Err(EBUSY);
            }

            data.path.clone()
        };

        let mut path = initial_path.clone();
        let mut b = w.reply(outbuf, usize::MAX)?;

        for name in w.names.clone() {
            match Self::walk_next(&mut b, &path, name) {
                Ok(new_path) => path = new_path,
                Err(e) => {
                    if b.wrapper_write_count() == 0 {
                        return Err(e);
                    }
                    break;
                }
            }
        }

        let len = b.finish();

        // Allocate the new node before taking locks.
        let node = RBTree::try_allocate_node(w.new_fid, IdData::new(path))?;

        // Try to store the file into the table again. We need to recheck the state of the
        // descriptor table.
        {
            let mut guard = self.inner.lock();

            let data = guard.id_table.get(&w.fid).ok_or(EBADF)?;

            // Check if the id wasn't clunked and walked to a different path.
            if initial_path != data.path {
                return Err(EINVAL);
            }

            // Don't allow reassigning an existing fid (except the one we're using).
            if w.new_fid != w.fid && guard.id_table.get(&w.new_fid).is_some() {
                return Err(EBUSY);
            }

            // Add new fid to table, and free the old one after releasing the lock.
            let old = guard.id_table.insert(node);
            drop(guard);
            drop(old);
        }

        Ok(len)
    }

    pub(crate) fn dispatch(&self, outbuf: &mut [u8], tag: u16, pdu: &[u8]) -> Result<usize> {
        let op = match parse(pdu) {
            Ok(r) => r,
            Err(e) => return error(outbuf, tag, e),
        };

        let res = match &op {
            Operation::Bad => Err(EOPNOTSUPP),
            Operation::Version(v) => self.version(outbuf, v),
            Operation::GetAttr(a) => self.get_attr(outbuf, a),
            Operation::Clunk(c) => self.clunk(outbuf, c),
            Operation::Open(o) => self.open(outbuf, o),
            Operation::Read(r) => self.read(outbuf, r),
            Operation::ReadDir(r) => self.readdir(outbuf, r),
            Operation::ReadLink(r) => self.readlink(outbuf, r),
            Operation::Attach(a) => self.attach(outbuf, a),
            Operation::Walk(w) => self.walk(outbuf, w),
        };

        res.or_else(|e| error(outbuf, tag, e))
    }
}

struct IdData {
    path: fs::Path,
    file: Option<ARef<File>>,
}

impl IdData {
    fn new(path: fs::Path) -> Self {
        Self { path, file: None }
    }
}

fn qid(inode: &fs::INode) -> Qid {
    Qid {
        ftype: match inode.kind() {
            fs::inode_kind::DIR => 0x80,
            fs::inode_kind::LNK => 0x02,
            _ => 0,
        },
        version: 0,
        path: inode.number(),
    }
}

fn dirent(name: &[u8], ino: u64, offset: u64, ftype: u8) -> DirEntry<'_> {
    use file::dirent::*;
    DirEntry {
        qid: Qid {
            ftype: match ftype as u32 {
                DT_DIR => 0x80,
                DT_REG => 0,
                DT_LNK => 0x02,
                _ => 0,
            },
            version: 0,
            path: ino,
        },
        offset,
        ftype,
        name,
    }
}

fn attrs(inode: &fs::INode, mask: u64) -> Attributes {
    let access = inode.access_permissions() as u32;
    Attributes {
        result_mask: mask,
        qid: qid(inode),
        st_mode: (access | inode.kind() as u32),
        st_nlink: 1,
        st_size: inode.size(),
        st_blksize: 512,
        st_blocks: ((inode.size() + 511) / 512),
        ..Attributes::default()
    }
}
