// SPDX-License-Identifier: GPL-2.0

//! Hyper-V interfaces.
//!
//! C header: [`include/linux/hyperv.h`](../../../../include/linux/hyperv.h)

use crate::{
    bindings, error::to_result, error::Result, types::ForeignOwnable, types::Opaque,
    types::ScopeGuard,
};
pub use bindings::{heartbeat_msg_data, icmsg_hdr};
use core::marker::PhantomData;

pub mod vmbus;

/// Size of the C `vmbuspipe_hdr` type.
pub const BUSPIPE_HDR_SIZE: usize = core::mem::size_of::<bindings::vmbuspipe_hdr>();

/// Size of the C `vmbuspipe_hdr` and `icmsg_hdr` types, which are the beginning of packets
/// received through a [`Channel`].
pub const ICMSG_HDR: usize = BUSPIPE_HDR_SIZE + core::mem::size_of::<bindings::icmsg_hdr>();

/// Specifies the type of a packet to be sent via [`Channel::send_packet`] and variants.
#[repr(u32)]
pub enum PacketType {
    /// Data is included in the packet.
    DataInband = bindings::vmbus_packet_type_VM_PKT_DATA_INBAND,
}

/// Channel callback modes.
///
/// These are used in [`ChannelToOpenl:set_read_mode`].
#[repr(u32)]
pub enum CallMode {
    /// Callback called from taslket and should read channel until empty. Interrupts from the host
    /// are masked while read is in process (default).
    Batched = bindings::vmbus_channel_hv_callback_mode_HV_CALL_BATCHED,

    /// Callback called from tasklet (softirq).
    Direct = bindings::vmbus_channel_hv_callback_mode_HV_CALL_DIRECT,
    // TODO: Bring this back eventually.
    //
    // N.B. When we do bring this back, the context data associated with the channel callback will
    // need to be shared as ISRs can be called concurrently from multiple CPUs.
    //    /// Callback called in interrupt context and must invoke its own deferred processing. Host
    //    /// interrupts are disabled and must be re-enabled when ring is empty.
    //    Isr = bindings::vmbus_channel_hv_callback_mode_HV_CALL_ISR,
}

/// A channel on a vmbus bus that is ready to be opened.
///
/// Wraps the kernel's C `struct vmbus_channel` when it's in `CHANNEL_OPEN_STATE` state.
///
/// # Invariants
///
/// `0` points to a valid channel that is ready to be opened. Additionally, this instance of
/// [`ChannelToOpen`] holds a refcount increment in `0`.
pub struct ChannelToOpen(*mut bindings::vmbus_channel);

// SAFETY: This just wraps a vmbus channel, which can be used from any thread/cpu.
unsafe impl Send for ChannelToOpen {}

// SAFETY: This just wraps a vmbus channel, which can be used from any thread/cpu.
unsafe impl Sync for ChannelToOpen {}

impl ChannelToOpen {
    /// Creates a new instance of a `ChannelToOpen`.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a valid new channel.
    unsafe fn new(ptr: *mut bindings::vmbus_channel) -> Self {
        // INVARIANT: Incrementing the refcount on `ptr`, so this instances owns the increment.
        //
        // SAFETY: The safety requirements ensure that `ptr` is valid, so we can increment the
        // refocunt.
        unsafe { bindings::kobject_get(&mut (*ptr).kobj) };
        Self(ptr)
    }

    /// Sets the channel's read mode.
    pub fn set_read_mode(&mut self, mode: CallMode) {
        // SAFETY: `self.0` is valid and the channel is not opened yet, so it is safe to change the
        // read mode.
        unsafe { bindings::set_channel_read_mode(self.0, mode as _) };
    }

    /// Opens the channel.
    pub fn open<H: ChannelDataHandler>(
        self,
        send_ringbuffer_size: usize,
        recv_ringbuffer_size: usize,
        userdata: &[u8],
        context: H::Context,
    ) -> Result<ChannelCloser<H::Context>> {
        let context_ptr = context.into_foreign();
        let guard = ScopeGuard::new(|| {
            // SAFETY: `contex_ptr` just came from a call to `into_pointer` and if the guard runs,
            // there won't be any users of it anymore.
            unsafe { H::Context::from_foreign(context_ptr) };
        });
        let ptr = self.0;
        // SAFETY: By the type invariants, we know that `self.0` is valid and that the channel is
        // not opened yet. The userdata pointers are also valid for the duration of this call,
        // given that the lifetime on the shared borrow guarantees it.
        to_result(unsafe {
            bindings::vmbus_open(
                ptr,
                send_ringbuffer_size.try_into()?,
                recv_ringbuffer_size.try_into()?,
                userdata.as_ptr() as _,
                userdata.len().try_into()?,
                Some(Self::callback::<H>),
                context_ptr as _,
            )
        })?;
        core::mem::forget(self);
        guard.dismiss();
        // INVARIANT: We are transferring the ownership of the refcount increment to the
        // `ChannelCloser` instance.
        Ok(ChannelCloser {
            ptr,
            context: context_ptr,
            _p: PhantomData,
        })
    }

    unsafe extern "C" fn callback<H: ChannelDataHandler>(
        chan: *mut bindings::vmbus_channel,
        context: *mut core::ffi::c_void,
    ) {
        // SAFETY: Given that the channel can only be in batched and direct call modes, the
        // callback is guaranteed to not run concurrently, so it's safe to borrow the context data
        // mutably.
        let mut data = unsafe { H::Context::borrow_mut(context) };

        // SAFETY: The channel is valid by the C contract, so it's safe to cast it to the
        // transparent `Channel` type.
        let channel = unsafe { &*(chan as *const Channel) };
        H::handle_data(&mut data, channel)
    }
}

impl Drop for ChannelToOpen {
    fn drop(&mut self) {
        // SAFETY: The type invariants guarantee that this object holds a reference to the channel.
        unsafe { bindings::kobject_put(&mut (*self.0).kobj) };
    }
}

/// Closes the channel and frees any associated resources when it goes out of scope.
///
/// # Invariants
///
/// `ptr` points to a valid channel that is opened. Additionally, this instance of [`ChannelCloser`]
/// holds a refcount increment in `ptr`.
pub struct ChannelCloser<T: ForeignOwnable> {
    ptr: *mut bindings::vmbus_channel,
    context: *const core::ffi::c_void,
    _p: PhantomData<T>,
}

// SAFETY: This wraps a vmbus channel, which can be used from any thread/cpu. It also holds context
// data, so it is `Send` as long as the context data also is.
unsafe impl<T: ForeignOwnable + Send> Send for ChannelCloser<T> {}

// SAFETY: This wraps a vmbus channel, which can be used from any thread/cpu. It also holds context
// data, so it is `Sync` as long as the context data also is.
unsafe impl<T: ForeignOwnable + Sync> Sync for ChannelCloser<T> {}

impl<T: ForeignOwnable> ChannelCloser<T> {
    /// Manually closes the channel and returns a new channel and the data.
    ///
    /// The returned values can be reused later to re-open the channel.
    pub fn close(self) -> (ChannelToOpen, T) {
        // SAFETY: The type invariants guarantee that the channel is valid and opened.
        unsafe { bindings::vmbus_close(self.ptr) };
        // SAFETY: `self.context` came from a previous call to `into_foreign`. Having closed the
        // channel above, we know there are no more references to it.
        let data = unsafe { T::from_foreign(self.context) };

        // INVARIANT: The increment of the refcount is transferred to the `ChannelToOpen` instance.
        let new_chan = ChannelToOpen(self.ptr);
        core::mem::forget(self);
        (new_chan, data)
    }
}

impl<T: ForeignOwnable> Drop for ChannelCloser<T> {
    fn drop(&mut self) {
        // SAFETY: The type invariants guarantee that the channel is valid and opened.
        unsafe { bindings::vmbus_close(self.ptr) };

        // SAFETY: The type invariants guarantee that this object holds a reference to the channel.
        unsafe { bindings::kobject_put(&mut (*self.ptr).kobj) };

        // SAFETY: `self.context` came from a previous call to `into_foreign`. Having closed the
        // channel above, we know there are no more references to it.
        unsafe { T::from_foreign(self.context) };
    }
}

/// A handler of data on a channel.
pub trait ChannelDataHandler {
    /// The context data associated with and made available to the handler.
    type Context: ForeignOwnable + Sync + Send;

    /// Called from interrupt context when the irq happens.
    fn handle_data(data: &mut Self::Context, chan: &Channel);
}

/// An open channel on a vmbus bus.
///
/// Wraps the kernel's C `struct vmbus_channel` when it's in `CHANNEL_OPENED_STATE` state.
///
/// # Invariants
///
/// The channel is opened.
#[repr(transparent)]
pub struct Channel(Opaque<bindings::vmbus_channel>);

impl Channel {
    /// Receives a packet from the channel.
    ///
    /// On success, returns the request id and the actual received size on success.
    pub fn recv_packet(&self, buf: &mut [u8]) -> Result<(u64, usize)> {
        let mut read_len = 0;
        let mut request_id = 0;

        // SAFETY: The channel is opened by the type invariants. All other pointers are valid for
        // the duration of this call.
        to_result(unsafe {
            bindings::vmbus_recvpacket(
                self.0.get(),
                buf.as_mut_ptr().cast(),
                buf.len().try_into()?,
                &mut read_len,
                &mut request_id,
            )
        })?;

        Ok((request_id, read_len as _))
    }

    /// Sends a packet on the channel.
    pub fn send_packet(&self, buf: &[u8], requestid: u64, packet_type: PacketType) -> Result {
        // SAFETY: The channel is opened by the type invariants. All other pointers are valid for
        // the duration of this call.
        to_result(unsafe {
            bindings::vmbus_sendpacket(
                self.0.get(),
                buf.as_ptr() as *mut _,
                buf.len().try_into()?,
                requestid,
                packet_type as _,
                0,
            )
        })
    }
}

/// Parses a string into a GUID.
///
/// This function is const, so it can convert string at compile time.
pub const fn guid(input: &[u8]) -> [u8; 16] {
    const fn hex(c: u8) -> u8 {
        c - if c >= b'0' && c <= b'9' {
            b'0'
        } else if c >= b'a' && c <= b'f' {
            b'a' - 10
        } else if c >= b'A' && c <= b'F' {
            b'A' - 10
        } else {
            panic!("Invalid guid");
        }
    }
    const INDICES: &[usize] = &[6, 4, 2, 0, 11, 9, 16, 14, 19, 21, 24, 26, 28, 30, 32, 34];
    let mut result = [0; 16];

    let mut i = 0;
    while i < INDICES.len() {
        result[i] = hex(input[INDICES[i]]) << 4 | hex(input[INDICES[i] + 1]);
        i += 1;
    }

    result
}
