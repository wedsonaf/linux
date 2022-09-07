// SPDX-License-Identifier: GPL-2.0

//! Management of read and write buffers.

use kernel::prelude::*;

#[derive(Clone, Copy)]
struct Wrapper {
    start: usize,
    cap: usize,
    cap_bias: usize,
    write_count: usize,
    finish: fn(&mut [u8], usize),
}

pub(crate) struct BufferWriter<'a> {
    pub(crate) data: &'a mut [u8],
    pub(crate) insert: usize,
    wrappers: [Wrapper; 3],
    wrapper_count: usize,
}

impl<'a> BufferWriter<'a> {
    pub(crate) fn new(data: &'a mut [u8]) -> Self {
        // TODO: Make sure that the size is capped at u32::MAX.
        Self {
            data,
            insert: 0,
            wrappers: [Wrapper {
                start: 0,
                write_count: 0,
                cap: usize::MAX,
                cap_bias: 0,
                finish: |_, _| (),
            }; 3],
            wrapper_count: 0,
        }
    }

    pub(crate) fn buffer(&mut self) -> &mut [u8] {
        // TODO: take cap into account.
        &mut self.data[self.insert..]
    }

    pub(crate) fn wrapper_write_count(&self) -> usize {
        if self.wrapper_count == 0 {
            return 0;
        }

        self.wrappers[self.wrapper_count - 1].write_count
    }

    pub(crate) fn wrapper_new<T: WrapperDetails>(&mut self, cap: usize) -> Result {
        if self.wrapper_count >= self.wrappers.len() {
            return Err(ENOSPC);
        }

        self.wrappers[self.wrapper_count] = Wrapper {
            cap,
            finish: T::finish,
            write_count: 0,
            start: self.insert,
            cap_bias: if T::IS_INCLUSIVE {
                0
            } else {
                core::mem::size_of::<T::CountType>()
            },
        };

        T::CountType::default().write_to_buffer(self)?;

        if self.wrapper_count > 0 {
            self.wrappers[self.wrapper_count - 1].write_count += 1;
        }

        self.wrapper_count += 1;
        Ok(())
    }

    pub(crate) fn wrapper_finish(&mut self) {
        if self.wrapper_count == 0 {
            return;
        }

        self.wrapper_count -= 1;
        let i = self.wrapper_count;
        (self.wrappers[i].finish)(
            &mut self.data[self.wrappers[i].start..self.insert],
            self.wrappers[i].write_count,
        );
    }

    pub(crate) fn finish(mut self) -> usize {
        while self.wrapper_count > 0 {
            self.wrapper_finish();
        }
        self.insert
    }

    pub(crate) fn write(&mut self, value: &(impl BufferWritable + ?Sized)) -> Result {
        let saved = self.insert;
        if let Err(e) = value.write_to_buffer(self) {
            self.insert = saved;
            return Err(e);
        }

        // Make sure we don't violate the cap of any wrapper.
        for w in &self.wrappers[..self.wrapper_count] {
            if self.insert - w.start - w.cap_bias > w.cap {
                self.insert = saved;
                return Err(ENOSPC);
            }
        }

        if self.wrapper_count > 0 {
            self.wrappers[self.wrapper_count - 1].write_count += 1;
        }

        Ok(())
    }
}

pub(crate) trait WrapperDetails {
    type CountType: BufferWritable + Default;
    const IS_INCLUSIVE: bool;
    fn finish(buf: &mut [u8], count: usize);
}

pub(crate) struct ByteCount;
impl WrapperDetails for ByteCount {
    type CountType = u32;
    const IS_INCLUSIVE: bool = false;
    fn finish(data: &mut [u8], _: usize) {
        let len = data.len() as u32 - 4;
        let mut t = BufferWriter::new(data);
        let _ = len.write_to_buffer(&mut t);
    }
}

pub(crate) struct InclusiveByteCount;
impl WrapperDetails for InclusiveByteCount {
    type CountType = u32;
    const IS_INCLUSIVE: bool = true;
    fn finish(data: &mut [u8], _: usize) {
        let len = data.len() as u32;
        let mut t = BufferWriter::new(data);
        let _ = len.write_to_buffer(&mut t);
    }
}

pub(crate) struct EntryCount;
impl WrapperDetails for EntryCount {
    type CountType = u16;
    const IS_INCLUSIVE: bool = false;
    fn finish(data: &mut [u8], c: usize) {
        let mut t = BufferWriter::new(data);
        let _ = (c as u16).write_to_buffer(&mut t);
    }
}

pub(crate) trait BufferWritable: Sync {
    fn write_to_buffer(&self, b: &mut BufferWriter<'_>) -> Result;
}

macro_rules! int_writable {
    ($t:ty) => {
        impl BufferWritable for $t {
            fn write_to_buffer(&self, b: &mut BufferWriter<'_>) -> Result {
                let a = &mut *b.data;
                if a.len() - b.insert < core::mem::size_of::<Self>() {
                    return Err(ENOSPC);
                }
                for i in 0..core::mem::size_of::<Self>() {
                    a[b.insert + i] = (*self >> 8 * i) as u8;
                }
                b.insert += core::mem::size_of::<Self>();
                Ok(())
            }
        }

        impl BufferReadable<'_> for $t {
            fn read_from_buffer(b: &mut Buffer<'_>) -> Result<Self> {
                let a = b.data;
                if a.len() < core::mem::size_of::<Self>() {
                    return Err(ENOSPC);
                }
                let mut v = 0;
                for i in 0..core::mem::size_of::<Self>() {
                    v |= (a[i] as Self) << (i * 8)
                }
                b.data = &b.data[core::mem::size_of::<Self>()..];
                Ok(Self::from_le(v))
            }
        }
    };
}

int_writable!(u8);
int_writable!(u16);
int_writable!(u32);
int_writable!(u64);

impl BufferWritable for str {
    fn write_to_buffer(&self, b: &mut BufferWriter<'_>) -> Result {
        self.as_bytes().write_to_buffer(b)
    }
}

impl BufferWritable for [u8] {
    fn write_to_buffer(&self, b: &mut BufferWriter<'_>) -> Result {
        let len = self.len();
        if len > u16::MAX.into() {
            return Err(ENOSPC);
        }
        (len as u16).write_to_buffer(b)?;
        let a = &mut *b.data;
        if a.len() - b.insert < len {
            return Err(ENOSPC);
        }
        a[b.insert..][..len].copy_from_slice(self);
        b.insert = b.insert.wrapping_add(len);
        Ok(())
    }
}

#[derive(Clone)]
pub(crate) struct Buffer<'a> {
    pub(crate) data: &'a [u8],
}

impl<'a> Buffer<'a> {
    pub(crate) fn read<T: BufferReadable<'a>>(&mut self) -> Result<T> {
        T::read_from_buffer(self)
    }
}

pub(crate) trait BufferReadable<'a>: Sized {
    fn read_from_buffer(b: &mut Buffer<'a>) -> Result<Self>;
}

impl<'a> BufferReadable<'a> for &'a [u8] {
    fn read_from_buffer(b: &mut Buffer<'a>) -> Result<Self> {
        let len: u16 = b.read()?;
        let len = len.into();
        let a = b.data;
        if a.len() < len {
            return Err(ENOSPC);
        }
        let v = &b.data[..len];
        b.data = &b.data[len..];
        Ok(v)
    }
}

impl<'a> BufferReadable<'a> for &'a str {
    fn read_from_buffer(b: &mut Buffer<'a>) -> Result<Self> {
        let s: &[u8] = b.read()?;
        Ok(core::str::from_utf8(s)?)
    }
}

pub(crate) fn reserve(size: usize) -> impl BufferWritable {
    generic_writer(move |b| {
        if b.data.len() - b.insert < size {
            return Err(ENOSPC);
        }
        b.insert = b.insert.wrapping_add(size);
        Ok(())
    })
}

pub(crate) fn generic_writer(
    w: impl Sync + Fn(&mut BufferWriter<'_>) -> Result,
) -> impl BufferWritable {
    struct GenericWriter<T: Sync + Fn(&mut BufferWriter<'_>) -> Result> {
        writer: T,
    }

    impl<T: Sync + Fn(&mut BufferWriter<'_>) -> Result> BufferWritable for GenericWriter<T> {
        fn write_to_buffer(&self, b: &mut BufferWriter<'_>) -> Result {
            (self.writer)(b)
        }
    }

    GenericWriter { writer: w }
}
