// SPDX-License-Identifier: GPL-2.0

//! 9P protocol definitions.

use super::buffer::*;
use kernel::prelude::*;

const TLOPEN: u8 = 12;
const TREADLINK: u8 = 22;
const TGETATTR: u8 = 24;
const TREADDIR: u8 = 40;
const TVERSION: u8 = 100;
const TATTACH: u8 = 104;
const TWALK: u8 = 110;
const TREAD: u8 = 116;
const TCLUNK: u8 = 120;

const RLERROR: u8 = 7;

fn new_buffer_writer(data: &mut [u8], op: u8, tag: u16) -> Result<BufferWriter<'_>> {
    let mut b = BufferWriter::new(data);
    b.wrapper_new::<InclusiveByteCount>(u32::MAX as usize)?;
    b.write(&op)?;
    b.write(&tag)?;
    Ok(b)
}

#[derive(Clone)]
pub(crate) struct Names<'a> {
    buffer: Buffer<'a>,
}

impl<'a> Iterator for Names<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        let name: &[u8] = self.buffer.read().ok()?;
        core::str::from_utf8(name).ok()
    }
}

impl<'a> BufferReadable<'a> for Names<'a> {
    fn read_from_buffer(b: &mut Buffer<'a>) -> Result<Self> {
        let count: u16 = b.read()?;
        let ret = Self { buffer: b.clone() };
        for _ in 0..count {
            let s: &[u8] = b.read()?;
            core::str::from_utf8(s)?;
        }
        Ok(ret)
    }
}

macro_rules! impl_writable {
    ($sname:ident $(<$lt:lifetime>)?, [ $($name:ident : $typ:ty),+ $(,)?] $(,)?) => {
        #[derive(Default)]
        pub(crate) struct $sname $(<$lt>)? {
            $(pub(crate) $name: $typ),*
        }

        impl $(<$lt>)? BufferWritable for $sname $(<$lt>)? {
            fn write_to_buffer(&self, b: &mut BufferWriter<'_>) -> Result {
                $(self.$name.write_to_buffer(b)?;)*
                Ok(())
            }
        }
    };
}

impl_writable!(Qid, [ftype: u8, version: u32, path: u64]);
impl_writable!(
    DirEntry<'a>,
    [qid: Qid, offset: u64, ftype: u8, name: &'a [u8]]
);
impl_writable!(
    Attributes,
    [
        result_mask: u64,
        qid: Qid,
        st_mode: u32,
        st_uid: u32,
        st_gid: u32,
        st_nlink: u64,
        st_rdev: u64,
        st_size: u64,
        st_blksize: u64,
        st_blocks: u64,
        st_atime_sec: u64,
        st_atime_nsec: u64,
        st_mtime_sec: u64,
        st_mtime_nsec: u64,
        st_ctime_sec: u64,
        st_ctime_nsec: u64,
        st_btime_sec: u64,
        st_btime_nsec: u64,
        st_gen: u64,
        st_data_version: u64,
    ]
);

macro_rules! impl_reply {
    ($op: expr, [$($rname:ident : $rtyp:ty),* $(,)?]) => {
        pub(crate) fn reply(&self, data: &mut [u8], $($rname:$rtyp),*) -> Result<usize> {
            #[allow(unused_mut)]
            let mut b = new_buffer_writer(data, $op + 1, self.tag)?;
            $(($rname).write_to_buffer(&mut b)?;)*
                Ok(b.finish())
        }
    };
    ($op: expr, $wrapper_type:ty) => {
        pub(crate) fn reply<'z>(&self, data: &'z mut [u8], cap: usize) -> Result<BufferWriter<'z>> {
            let mut b = new_buffer_writer(data, $op + 1, self.tag)?;
            b.wrapper_new::<$wrapper_type>(cap)?;
            Ok(b)
        }
    };
}

macro_rules! lt_type_name {
    ($name:ident) => { $name<'_> };
    ($name:ident <$lt:lifetime>) => { $name<$lt> };
}

macro_rules! impl_struct {
    ($sname:ident $(<$lt:lifetime>)?, $op:expr, [ $($name:ident : $typ:ty),+ $(,)?] $($t:tt)*) => {
        pub(crate) struct $sname $(<$lt>)? {
            tag: u16,
            $(
                #[allow(dead_code)]
                pub(crate) $name: $typ
            ),*
        }

        impl $(<$lt>)? $sname $(<$lt>)? {
            fn parse(tag: u16, mut buf: lt_type_name!(Buffer$(<$lt>)?)) -> Result<Self> {
                let obj = Self {
                    tag,
                    $($name: buf.read()?,)*
                };
                // Reject the PDU if it has trailing data.
                if !buf.data.is_empty() {
                    return Err(EOPNOTSUPP);
                }
                Ok(obj)
            }

            impl_reply!($op $($t)*);
        }
    }
}

macro_rules! define_operations {
    ($({$sname:ident $(<$lt:lifetime>)?, $op:ident, $($t:tt)*})*) => {
        pub(crate) enum Operation<'a> {
            $($sname($sname$(<$lt>)?),)*
            Bad,
        }

        pub(crate) fn parse(pdu: &[u8]) -> Result<Operation<'_>> {
            let mut buf = Buffer { data: &*pdu };
            let op: u8 = buf.read()?;
            let tag: u16 = buf.read()?;
            Ok(match op {
                $($op => Operation::$sname($sname::parse(tag, buf)?),)*
                _ => Operation::Bad,
            })
        }
    };
}

macro_rules! define_all {
    ($({ $($t:tt)* }),* $(,)?) => {
        $(impl_struct!($($t)*);)*
        define_operations!($({$($t)*})*);
    };
}

define_all! {
    { Version<'a>, TVERSION, [msize: u32, ver: &'a str], [msize: u32, ver: &str] },
    { GetAttr, TGETATTR, [fid: u32, request_mask: u64], [attrs: &Attributes] },
    { Clunk, TCLUNK, [fid: u32], [] },
    { Open, TLOPEN, [fid: u32, flags: u32], [qid: &Qid, iounit: u32] },
    { Read, TREAD, [fid: u32, offset: u64, size: u32], ByteCount },
    { ReadDir, TREADDIR, [fid: u32, offset: u64, size: u32], ByteCount },
    { ReadLink, TREADLINK, [fid: u32], [name: &[u8]] },
    { Walk<'a>, TWALK, [fid: u32, new_fid: u32, names: Names<'a>], EntryCount },
    { Attach<'a>, TATTACH, [fid: u32, afid: u32, uname: &'a str, aname: &'a str, n_uname: u32],
        [qid: &Qid] },
}

pub(crate) fn get_op_tag(pdu: &[u8]) -> Result<(u8, u16)> {
    let mut buf = Buffer { data: &*pdu };
    Ok((buf.read()?, buf.read()?))
}

pub(crate) fn error(data: &mut [u8], tag: u16, e: Error) -> Result<usize> {
    let mut b = new_buffer_writer(data, RLERROR, tag)?;
    b.write(&(-e.to_kernel_errno() as u32))?;
    Ok(b.finish())
}
