// SPDX-License-Identifier: GPL-2.0

//! Rust echo server sample.

use kernel::{
    kasync::executor::{
        local::{AutoJoinHandle, Local},
        Executor,
    },
    kasync::net::{TcpListener, TcpStream},
    net::{self, Ipv4Addr, SocketAddr, SocketAddrV4},
    prelude::*,
    sync::{Ref, RefBorrow},
};

async fn echo_server(stream: TcpStream) -> Result {
    let mut buf = [0u8; 1024];
    loop {
        let n = stream.read(&mut buf).await?;
        if n == 0 {
            return Ok(());
        }
        stream.write_all(&buf[..n]).await?;
    }
}

async fn accept_loop(listener: TcpListener, executor: Ref<impl Executor>) {
    loop {
        if let Ok(stream) = listener.accept().await {
            let _ = executor.as_ref_borrow().spawn(echo_server(stream));
        }
    }
}

fn start_listener(ex: RefBorrow<'_, impl Executor + Send + Sync + 'static>) -> Result {
    let addr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::ANY, 8080));
    let listener = TcpListener::try_new(net::init_ns(), &addr)?;
    ex.spawn(accept_loop(listener, ex.into()))?;
    Ok(())
}

struct RustEchoServer {
    _ex_handle: AutoJoinHandle,
}

impl kernel::Module for RustEchoServer {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        let handle = Local::try_new()?.run_on_dedicated_thread(fmt!("echo-server-executor"))?;
        start_listener(handle.executor())?;
        Ok(Self { _ex_handle: handle })
    }
}

module! {
    type: RustEchoServer,
    name: b"rust_echo_server",
    author: b"Rust for Linux Contributors",
    description: b"Rust tcp echo sample",
    license: b"GPL v2",
}
