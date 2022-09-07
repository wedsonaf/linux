// SPDX-License-Identifier: GPL-2.0

//! 9P file server.

use kernel::{
    c_str,
    file::{self, File},
    kasync::executor::{workqueue::Executor as WqExecutor, AutoStopHandle, Executor},
    kasync::mutex::Mutex,
    kasync::net::{TcpListener, TcpStream},
    net::{self, Ipv4Addr, SocketAddr, SocketAddrV4},
    prelude::*,
    spawn_task,
    sync::{Ref, RefBorrow},
};

mod buffer;
mod localfs;
mod protocol;

use buffer::*;

struct ConnInner {
    err: Result,
}

struct Connection {
    stream: TcpStream,
    fs: localfs::Server,
    inner: Mutex<ConnInner>,
}

impl Connection {
    async fn write(&self, buf: &[u8]) {
        let mut inner = self.inner.lock().await;
        if inner.err.is_err() {
            // A previous write failed so we won't even try this one.
            return;
        }
        let ret = self.stream.write_all(buf).await;
        if ret.is_err() {
            // Store away the error.
            inner.err = ret;
        }
    }

    async fn write_result(&self, cb: impl FnOnce(&mut [u8]) -> Result<usize>) -> Result {
        let mut outbuf = [0u8; 1024];
        let len = cb(&mut outbuf)?;
        self.write(&outbuf[..len]).await;
        Ok(())
    }

    async fn next_pdu(&self, max_size: u32) -> Result<Box<[u8]>> {
        // Read the length.
        let mut len_in_bytes = [0u8; 4];
        self.stream.read_all(&mut len_in_bytes).await?;

        let len = u32::from_le_bytes(len_in_bytes).checked_sub(4).ok_or(EIO)?;
        if len > max_size {
            return Err(E2BIG);
        }

        // Allocate the buffer and read the rest.
        self.stream.alloc_read_exact(len as usize).await
    }

    async fn handle_pdu(self: Ref<Self>, tag: u16, pdu: Box<[u8]>) {
        let mut outbuf = [0u8; 1024];

        let len = match self.fs.dispatch(&mut outbuf, tag, &pdu) {
            Ok(l) => l,
            Err(e) => protocol::error(&mut outbuf, tag, e).unwrap(),
        };

        // Do the write under a mutex so that we can guarantee that the whole response is written.
        self.write(&outbuf[..len]).await;
    }

    async fn main_loop(
        stream: TcpStream,
        tree: ARef<File>,
        executor: Ref<impl Executor>,
    ) -> Result {
        // Allocate state for the connection.
        let conn = Ref::try_new(Connection {
            stream,
            fs: localfs::Server::new(tree),
            inner: Mutex::new(ConnInner { err: Ok(()) }),
        })?;

        let max_size;

        // The very first request must be a version one.
        let pdu = conn.next_pdu(1024).await?;
        let op = protocol::parse(&pdu)?;
        match op {
            protocol::Operation::Version(v) => {
                conn.write_result(|buf| localfs::Server::initial_version(buf, &v))
                    .await?;
                max_size = v.msize;
            }
            _ => return Err(EINVAL),
        }

        // Now we can handle other ops.
        loop {
            let pdu = conn.next_pdu(max_size).await?;
            let (_op, tag) = protocol::get_op_tag(&pdu)?;
            let res = spawn_task!(executor.as_ref_borrow(), conn.clone().handle_pdu(tag, pdu));
            if let Err(e) = res {
                conn.write_result(|b| protocol::error(b, tag, e)).await?;
            }
        }
    }
}

async fn accept_loop(
    listener: TcpListener,
    executor: Ref<impl Executor + Send + 'static>,
    f: ARef<File>,
) {
    loop {
        if let Ok(stream) = listener.accept().await {
            let res = spawn_task!(
                executor.as_ref_borrow(),
                Connection::main_loop(stream, f.clone(), executor.clone())
            );

            if let Err(e) = res {
                pr_debug!("Unable to spawn task for new connection: {:?}\n", e);
            }
        }
    }
}

fn start_listener(
    ex: RefBorrow<'_, impl Executor + Send + Sync + 'static>,
    f: ARef<File>,
) -> Result {
    let addr = SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::ANY, 564));
    let listener = TcpListener::try_new(net::init_ns(), &addr)?;
    spawn_task!(ex, accept_loop(listener, ex.into(), f))?;
    Ok(())
}

struct Server {
    _handle: AutoStopHandle<dyn Executor>,
}

impl kernel::Module for Server {
    fn init(_name: &'static CStr, _module: &'static ThisModule) -> Result<Self> {
        let handle = WqExecutor::try_new(kernel::workqueue::system())?;
        let f = File::open(
            c_str!("/"),
            file::flags::O_DIRECTORY | file::flags::O_RDONLY,
        )?;
        start_listener(handle.executor(), f)?;
        Ok(Self {
            _handle: handle.into(),
        })
    }
}

module! {
    type: Server,
    name: "k9pd",
    author: "Wedson Almeida Filho <wedsonaf@gmail.com>",
    description: "Plan 9 file system server",
    license: "GPL",
}
