#include <poll.h>
#include <pthread.h>

#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/signalfd.h>
#include <sys/epoll.h>
#include <fcntl.h>
#include <linux/android/binder.h>

#include "../kselftest_harness.h"

#define BINDER_TEST_LIST(__name, ...) \
	TEST(__name) { \
		test_func *fs[] = { __VA_ARGS__ }; \
		int ret = run_all(_metadata, fs, sizeof(fs) / sizeof(*fs)); \
		ASSERT_EQ(0, ret); \
	} \

#define BINDER_TEST(__name, ...) \
	static void __name##_inline(struct __test_metadata *, size_t, int); \
	BINDER_TEST_LIST(__name, __VA_ARGS__, __name##_inline) \
	static void __name##_inline(struct __test_metadata *_metadata, \
				    size_t index, int comm_fd) \

typedef void test_func(struct __test_metadata *_metadata,
		       size_t index, int comm_fd);

struct process_state {
	pid_t pid;
	bool is_waiting;
};

struct processes_state {
	size_t count;
	size_t waiting;
	size_t remaining;
	struct process_state *proc;
	struct pollfd *fds;
};

static const char* default_driver_name = "./binder";
static size_t default_mapped_size = 4096;

static int start_process(struct __test_metadata *_metadata, test_func *func,
			 int fd, struct pollfd *to_close,
			 size_t to_close_count, pid_t *pid)
{
	size_t i;
	int error;
	pid_t ret = fork();
	switch (ret) {
	case 0:
		for (i = 0; i < to_close_count; i++)
			close(to_close[i].fd);
		func(_metadata, to_close_count, fd);
		exit(0);

	case -1:
		error = errno;
		perror("fork");
		close(fd);
		return error;

	default:
		close(fd);
		*pid = ret;
		return 0;
	}
}

static void state_cleanup(struct processes_state *state)
{
	size_t i;

	/* Close all sockets and kill all children. */
	for (i = 0; i < state->count; i++) {
		if (state->fds[i].fd != -1)
			close(state->fds[i].fd);
		if (state->proc[i].pid != -1)
			kill(state->proc[i].pid, SIGKILL);
	}

	/* Wait for children to exit. */
	for (size_t i = 0; i < state->count; i++)
		if (state->proc[i].pid != -1)
			waitpid(state->proc[i].pid, NULL, 0);

	free(state->proc);
	free(state->fds);
}

static int state_init(struct __test_metadata *_metadata,
		      struct processes_state *state,
		      test_func *fs[], size_t count)
{
	size_t i;
	int ret;

	memset(state, 0, sizeof(*state));

	state->proc = calloc(count, sizeof(*state->proc));
	if (!state->proc)
		return ENOMEM;

	state->fds = calloc(count + 1, sizeof(*state->fds));
	if (!state->fds) {
		free(state->proc);
		return ENOMEM;
	}

	state->count = count;
	state->remaining = count;

	for (i = 0; i < state->count; i++) {
		int socks[2];

		if (socketpair(PF_UNIX, SOCK_SEQPACKET, 0, socks) == -1) {
			ret = errno;
			perror("socketpair");
			state->count = i;
			state_cleanup(state);
			return ret;
		}

		state->fds[i].events = POLLIN | POLLERR | POLLHUP;
		state->fds[i].fd = socks[1];
		ret = start_process(_metadata, fs[i], socks[0], state->fds, i,
				    &state->proc[i].pid);
		if (ret) {
			state->count = i;
			state_cleanup(state);
			return ret;
		}
	}

	return 0;
}

static int create_signalfd(void)
{
	sigset_t mask;
	sigemptyset(&mask);
	sigaddset(&mask, SIGCHLD);

	if (sigprocmask(SIG_BLOCK, &mask, NULL) == -1)
		return -1;

	return signalfd(-1, &mask, SFD_NONBLOCK);
}

static int handle_signals(struct processes_state *state)
{
	size_t i;
	pid_t pid;
	int status;

	/* Loop while there are pending signals. */
	while ((pid = waitpid(-1, &status, WNOHANG)) > 0) {

		/* Find the index of the child responsible for signal. */
		for (i = 0; i < state->count; i++) {
			if (pid == state->proc[i].pid)
				break;
		}

		if (i == state->count)
			break;

		/* Close communication fd. */
		if (state->fds[i].fd != -1) {
			close(state->fds[i].fd);
			state->fds[i].fd = -1;
		}

		/* Erase the pid of the child from our state and fail if the
		 * child exited with a non-zero exit value or due to a
		 * signal. */
		state->proc[i].pid = -1;
		if (WIFSIGNALED(status))
			return 1;

		if (WIFEXITED(status) && WEXITSTATUS(status) != 0)
			return WEXITSTATUS(status);

		/* Decrement the number of remaining children. */
		state->remaining--;
	}

	return 0;
}

static int handle_data(struct processes_state *state)
{
	size_t i;
	size_t j;

	for (i = 0; i < state->count; i++) {
		char c;

		if (state->fds[i].revents == 0)
			continue;

		switch (read(state->fds[i].fd, &c, 1)) {
		case 0:
			close(state->fds[i].fd);
			state->fds[i].fd = -1;
			break;

		case -1:
			return errno;

		default:
			/* Received a ping from this process. Only respond when
			 * all processes have pinged. */
			if (state->proc[i].is_waiting)
				break;
			state->proc[i].is_waiting = true;
			state->waiting++;
			if (state->waiting < state->count)
				break;

			/* Wake all processes up. */
			for (j = 0; j < state->count; j++) {
				state->proc[j].is_waiting = false;
				write(state->fds[j].fd, &c, 1);
			}
			state->waiting = 0;
		}
	}

	return 0;
}

static int run_all(struct __test_metadata *_metadata,
		   test_func *fs[], size_t count)
{
	struct processes_state state;
	int ret;
	int sfd = -1;

	/* Start all processes. */
	ret = state_init(_metadata, &state, fs, count);
	if (ret)
		return ret;

	/* Create signalfd to get signals through an fd. */
	sfd = create_signalfd();
	if (sfd == -1) {
		ret = errno;
		perror("create_signalfd");
		goto exit;
	}

	state.fds[count].fd = sfd;
	state.fds[count].events = POLLIN;

	/* Loop until all processes have exited. */
	while (state.remaining) {
		ret = poll(state.fds, count + 1, -1);
		if (ret == -1) {
			ret = errno;
			goto exit;
		}

		ret = handle_data(&state);
		if (ret)
			goto exit;

		/* Check if a child exited. */
		if (state.fds[count].revents != 0) {
			struct signalfd_siginfo si;

			/* Consume the contents of the signalfd. */
			if (read(sfd, &si, sizeof(si)) != sizeof(si))
				continue;

			/* Consume all signals. */
			ret = handle_signals(&state);
			if (ret)
				goto exit;
		}

	}

exit:
	if (sfd != -1)
		close(sfd);
	state_cleanup(&state);
	return ret;
}

struct buffer {
	char *orig;
	char *next;
	size_t size;
};

static void *alloc(size_t size)
{
	void *ptr = malloc(size);
	if (!ptr) {
		fprintf(stderr, "Allocation of %zu bytes failed\n", size);
		exit(1);
	}
	return ptr;
}

static void buffer_init(struct buffer *b, size_t size)
{
	b->orig = alloc(size);
	b->next = b->orig;
	b->size = size;
}

static void buffer_free(struct buffer *b)
{
	free(b->orig);
	b->orig = NULL;
	b->next = NULL;
	b->size = 0;
}

static void *__buffer_advance(struct buffer *b, size_t size)
{
	void *ret = b->next;
	if (size > b->size)
		return NULL;

	b->next += size;
	b->size -= size;
	return ret;
}

#define ASSERT_BUFFER_EMPTY(__b) \
	ASSERT_EQ(0, (__b)->size) { \
		TH_LOG("Expected empty buffer, still have %zu bytes\n", \
		       (__b)->size); \
	}

#define ASSERT_BUFFER_ADVANCE(__b, __size) \
	({ \
		void *ptr = __buffer_advance(__b, __size); \
		ASSERT_NE(NULL, ptr) { \
			TH_LOG("Expected at least %zu bytes, only got %zu", \
				__size, (__b)->size); \
		} \
		ptr; \
	})

#define ASSERT_BUFFER_EQ(__b, __type, __value) \
	do { \
		__type * ptr = ASSERT_BUFFER_ADVANCE(__b, sizeof(__type)); \
		ASSERT_EQ(__value, *ptr); \
	} while(0) \

#define ASSERT_WRITE_ALL(__data) \
	ASSERT_EQ(sizeof(__data), write_buffer(&ctx, &__data, sizeof(__data)));

static int set_blocking(int fd, bool blocking)
{
        int flags = fcntl(fd, F_GETFL, 0);
        if (flags == -1)
		return errno;

        if (blocking)
                flags &= ~O_NONBLOCK;
        else
                flags |= O_NONBLOCK;

        if (fcntl(fd, F_SETFL, flags) == -1)
		return errno;

	return 0;
}

static int open_driver(const char *name)
{
	if (!name) {
		name = default_driver_name;
	}

	int fd = open(name, O_RDWR);
	if (fd == -1) {
		perror("open");
		exit(1);
	}

	return fd;
}

static void *map_driver(int fd, size_t size)
{
	void *shared_ptr = mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
	if (shared_ptr == MAP_FAILED) {
		perror("mmap");
		exit(1);
	}

	return shared_ptr;
}

static int create_pipe(int fds[2])
{
	return pipe(fds) != 0 ? errno : 0;
}

static void ioctl_no_failure(int fd, unsigned long request, void *arg)
{
	int ret = ioctl(fd, request, arg);
	if (ret == -1) {
		perror("ioctl");
		exit(1);
	}
}

struct context {
	int fd;
	int comm;
	void *shared_ptr;
	size_t size;
	size_t index;
	struct __test_metadata *_metadata;
};

static void context_init(struct context *ctx, int comm, size_t size,
			 size_t index, struct __test_metadata *_metadata)
{
	struct binder_version v;

	ctx->comm = comm;
	ctx->size = size;
	ctx->fd = open_driver(NULL);
	ctx->shared_ptr = map_driver(ctx->fd, size);
	ctx->index = index;
	ctx->_metadata = _metadata;

	ioctl_no_failure(ctx->fd, BINDER_VERSION, &v);
}

static int prepare_epoll(struct context *ctx)
{
	int epfd = epoll_create(1);
	if (epfd == -1)
		return -errno;

	struct epoll_event ev = {
		.events = EPOLLIN,
		.data.ptr = ctx,
	};

	if (epoll_ctl(epfd, EPOLL_CTL_ADD, ctx->fd, &ev) == -1) {
		int ret = -errno;
		close(epfd);
		return ret;
	}

	return epfd;
}

static void context_sync(struct context *ctx)
{
	char buf = 1;

	/* Send ping. */
	if (write(ctx->comm, &buf, 1) == -1) {
		perror("write");
		exit(1);
	}

	/* Get response. */
	if (read(ctx->comm, &buf, 1) == -1) {
		perror("read");
		exit(1);
	}
}

static ssize_t read_no_alloc(struct context *ctx, void *ptr, size_t size)
{
	struct binder_write_read b = {
		.read_size = size,
		.read_buffer = (binder_uintptr_t)ptr,
	};
	int ret = ioctl(ctx->fd, BINDER_WRITE_READ, &b);
	return ret == -1 ? -errno : b.read_consumed;
}

static struct buffer read_buffer(struct context *ctx, size_t size)
{
	struct buffer ret;
	buffer_init(&ret, size);
	struct binder_write_read b = {
		.read_size = size,
		.read_buffer = (binder_uintptr_t)ret.orig,
	};
	ioctl_no_failure(ctx->fd, BINDER_WRITE_READ, &b);
	ret.size = b.read_consumed;
	return ret;
}

static ssize_t write_buffer(struct context *ctx, const void *ptr, size_t size)
{
	struct binder_write_read b = {
		.write_size = size,
		.write_buffer = (binder_uintptr_t)ptr,
	};
	int ret = ioctl(ctx->fd, BINDER_WRITE_READ, &b);
	return ret == -1 ? -errno : b.write_consumed;
}

static struct buffer write_read_buffer(struct context *ctx,
				       const void *write_ptr,
				       size_t write_size, size_t read_size)
{
	struct buffer ret;
	buffer_init(&ret, read_size);
	struct binder_write_read b = {
		.write_size = write_size,
		.write_buffer = (binder_uintptr_t)write_ptr,
		.read_size = read_size,
		.read_buffer = (binder_uintptr_t)ret.orig,
	};
	ioctl_no_failure(ctx->fd, BINDER_WRITE_READ, &b);
	ret.size = b.read_consumed;
	return ret;
}

/**
 * Sets the file descriptor to nonblocking mode and read. Checks it fails with
 * EAGAIN error.
 */
TEST(nonblocking_read)
{
	struct context ctx;
	char buf[128];

	context_init(&ctx, -1, default_mapped_size, 0, _metadata);

	ASSERT_EQ(0, set_blocking(ctx.fd, false));
	ASSERT_EQ(-EAGAIN, read_no_alloc(&ctx, buf, sizeof(buf)));
}

/**
 * A manager tries to acquire handle 0 (itself). It must fail.
 */
TEST(manager_self_acquire)
{
	struct context ctx;

	context_init(&ctx, -1, default_mapped_size, 0, _metadata);

	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		uint32_t handle;
	} to_write = {
		.cmd = BC_ACQUIRE,
		.handle = 0,
	};

	ASSERT_EQ(-EINVAL, write_buffer(&ctx, &to_write, sizeof(to_write)));
}

/**
 * A manager tries to incref handle 0 (itself). It must fail.
 */
TEST(manager_self_increfs)
{
	struct context ctx;

	context_init(&ctx, -1, default_mapped_size, 0, _metadata);

	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		uint32_t handle;
	} to_write = {
		.cmd = BC_INCREFS,
		.handle = 0,
	};

	ASSERT_EQ(-EINVAL, write_buffer(&ctx, &to_write, sizeof(to_write)));
}

/**
 * Tries to send a transaction to the context manager when one is not
 * registered.
 */
TEST(no_manager)
{
	struct context ctx;
	struct buffer buf;

	context_init(&ctx, -1, default_mapped_size, 0, _metadata);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 123,
	};

	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_DEAD_REPLY);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);
}

static void server_closed(struct __test_metadata *_metadata,
			  size_t index, int comm_fd)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	close(ctx.fd);
	munmap(ctx.shared_ptr, ctx.size);

	context_sync(&ctx);
	context_sync(&ctx);
}

/**
 * Tries to send a transaction to the context manager when one has registered
 * but closed.
 */
BINDER_TEST(manager_dead, server_closed)
{
	struct context ctx;
	struct buffer buf;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 123,
	};

	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_DEAD_REPLY);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);
}

static void trivial_transaction_dead_server(struct context *ctx,
					    uint32_t handle, uint32_t code)
{
	struct __test_metadata *_metadata = ctx->_metadata;
	struct buffer buf;

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = handle,
		.tr.code = code,
	};

	ASSERT_EQ(sizeof(to_write),
		  write_buffer(ctx, &to_write, sizeof(to_write)));

	context_sync(ctx);

	buf = read_buffer(ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_DEAD_REPLY);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);
}

static void client_gets_dead_reply(struct __test_metadata *_metadata,
				   size_t index, int comm_fd)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	trivial_transaction_dead_server(&ctx, 0, 123);

	context_sync(&ctx);
}

/**
 * Sends a transaction to a recipient that receives it but exits the process
 * before replying. Ensures that the sender gets a completion indicating that
 * the recipient died.
 */
BINDER_TEST(server_dies, client_gets_dead_reply)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);
	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	close(ctx.fd);
	munmap(ctx.shared_ptr, ctx.size);

	context_sync(&ctx);
}

static void server_dies_queued_trans(struct __test_metadata *_metadata,
				     size_t index, int comm_fd)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);

	/* Wait for client(s) to queue transaction(s). */

	context_sync(&ctx);

	close(ctx.fd);
	munmap(ctx.shared_ptr, ctx.size);

	context_sync(&ctx);
}

/**
 * Sends a transaction to a recipient that exists while it is queued. Ensures
 * that the sender gets a completion indicating that the recipient died.
 */
BINDER_TEST_LIST(server_dies_trans_queued,
		 client_gets_dead_reply, server_dies_queued_trans);

/**
 * Sends two transactions to a recipient that exists while they arequeued.
 * Ensures that the senders get completions indicating that the recipient died.
 */
BINDER_TEST_LIST(server_dies_2_trans_queued, server_dies_queued_trans,
		 client_gets_dead_reply, client_gets_dead_reply);

/**
 * Sends a transaction to a recipient that receives it but exits the thread
 * before replying. Ensures that the sender gets a completion indicating that
 * the recipient thread exited.
 */
BINDER_TEST(server_thread_exits, client_gets_dead_reply)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);
	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	ioctl_no_failure(ctx.fd, BINDER_THREAD_EXIT, NULL);

	context_sync(&ctx);
}

static void trivial_transaction(struct context *ctx,
				uint32_t handle, uint32_t code)
{
	struct __test_metadata *_metadata = ctx->_metadata;
	struct buffer buf;
	struct binder_transaction_data *tr;

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = handle,
		.tr.code = code,
	};

	buf = write_read_buffer(ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(code + 1, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);
}

static void client_gets_dead_reply_then_succeeds(
		struct __test_metadata *_metadata, size_t index, int comm_fd)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	trivial_transaction_dead_server(&ctx, 0, 123);

	context_sync(&ctx);

	trivial_transaction(&ctx, 0, 125);

	context_sync(&ctx);
}

static void trivial_reply(struct context *ctx,
			  struct binder_transaction_data *tr)
{
	struct __test_metadata *_metadata = ctx->_metadata;
	struct buffer buf;

	struct __attribute__((__packed__)) {
		uint32_t cmd0;
		size_t ptr;
		uint32_t cmd1;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd0 = BC_FREE_BUFFER,
		.ptr = tr->data.ptr.buffer,
		.cmd1 = BC_REPLY,
		.tr.code = tr->code + 1,
	};

	buf = write_read_buffer(ctx, &to_write, sizeof(to_write), 512);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);
}

static void trivial_receive_reply(struct context *ctx, bool spawn)
{
	struct __test_metadata *_metadata = ctx->_metadata;
	struct buffer buf;
	struct binder_transaction_data *tr;

	/* Get transaction. */
	buf = read_buffer(ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, spawn ? BR_SPAWN_LOOPER : BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	/* Free buffer and reply to received transaction. */
	trivial_reply(ctx, tr);
	buffer_free(&buf);
}

/**
 * Sends a transaction to a recipient that receives it but exits the thread
 * before replying. Ensures that the sender gets a completion indicating that
 * the recipient thread exited. Then resurrects the thread and checks that
 * another transaction completes successfully.
 */
BINDER_TEST(server_thread_exits_then_resurrects,
	    client_gets_dead_reply_then_succeeds)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);

	ioctl_no_failure(ctx.fd, BINDER_THREAD_EXIT, NULL);

	context_sync(&ctx);

	/* Enter looper again. */
	ASSERT_WRITE_ALL(cmd);

	trivial_receive_reply(&ctx, false);

	context_sync(&ctx);
}

static void server_empty_reply(struct __test_metadata *_metadata,
			       size_t index, int comm_fd)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);
	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	trivial_reply(&ctx, tr);
	buffer_free(&buf);

	context_sync(&ctx);
}

/**
 * Client sends transaction and dies. Server receives and replies anyway.
 */
BINDER_TEST(client_dies, server_empty_reply)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 123,
	};

	ASSERT_WRITE_ALL(to_write);

	close(ctx.fd);
	munmap(ctx.shared_ptr, ctx.size);

	context_sync(&ctx);
	context_sync(&ctx);
}

static void client_transaction(struct __test_metadata *_metadata,
			       size_t index, int comm_fd)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);
	context_sync(&ctx);

	trivial_transaction(&ctx, 0, 123);

	context_sync(&ctx);
}

static void server_epoll_wait(struct __test_metadata *_metadata,
			      size_t index, int comm_fd)
{
	struct context ctx;
	uint32_t cmd;
	int epfd;
	char data[256];
	struct epoll_event ev;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);
	ASSERT_LE(0, epfd = prepare_epoll(&ctx));

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	ASSERT_EQ(0, set_blocking(ctx.fd, false));
	ASSERT_EQ(-EAGAIN, read_no_alloc(&ctx, data, sizeof(data)));

	context_sync(&ctx);
	context_sync(&ctx);

	ASSERT_NE(-1, epoll_wait(epfd, &ev, 1, 250)) {
		TH_LOG("Failed to wait: %s", strerror(errno));
	}

	ASSERT_EQ(EPOLLIN, ev.events);
	ASSERT_EQ(&ctx, ev.data.ptr);

	trivial_receive_reply(&ctx, false);

	context_sync(&ctx);
}

static void client_epoll_wait(struct __test_metadata *_metadata,
			      size_t index, int comm_fd)
{
	struct context ctx;
	int epfd;
	char data[256];
	struct epoll_event ev;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	ASSERT_LE(0, epfd = prepare_epoll(&ctx));

	context_sync(&ctx);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 123,
	};

	ASSERT_WRITE_ALL(to_write);

	ASSERT_EQ(0, set_blocking(ctx.fd, false));
	ASSERT_EQ(-EAGAIN, read_no_alloc(&ctx, data, sizeof(data)));

	context_sync(&ctx);

	ASSERT_NE(-1, epoll_wait(epfd, &ev, 1, 250)) {
		TH_LOG("Failed to wait: %s", strerror(errno));
	}

	ASSERT_EQ(EPOLLIN, ev.events);
	ASSERT_EQ(&ctx, ev.data.ptr);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);
}

/**
 * Simple transaction test. Sends a transaction to the context manager and gets
 * an empty reply back.
 */
BINDER_TEST_LIST(transaction, client_transaction, server_empty_reply);

/**
 * Server waits for transaction via a call to epoll_wait, and replies when one
 * is received. Client sends a transaction and wait for a reply.
 */
BINDER_TEST_LIST(epoll_wait_transaction, server_epoll_wait, client_transaction);

/**
 * Sends a transaction and waits for a reply via epoll.
 */
BINDER_TEST_LIST(epoll_wait_reply, server_empty_reply, client_epoll_wait)

/**
 * Sends a transaction to a sever waiting on epoll and waits for a reply via
 * epoll as well.
 */
BINDER_TEST_LIST(epoll_wait_trans_and_reply,
		 server_epoll_wait, client_epoll_wait);

/**
 * Sends a transaction to the context manager; before it replies, sends another
 * one from the same thread. Checks that the second one fails with
 * BR_FAILED_REPLY while the first one succeeds.
 */
BINDER_TEST(transaction_pending, server_empty_reply)
{
	struct context ctx;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 123,
	};

	ASSERT_WRITE_ALL(to_write);
	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);
	context_sync(&ctx);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_FAILED_REPLY);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);
}

/**
 * Sends a transaction to the context manager; before it replies, sends two
 * additional transactions from the same thread. Checks that the second one
 * fails with BR_FAILED_REPLY and that the third one is not processed (i.e., the
 * number of consumed bytes for the write operation is zero).
 */
BINDER_TEST(transaction_2pending, server_empty_reply)
{
	struct context ctx;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 123,
	};

	ASSERT_WRITE_ALL(to_write);
	ASSERT_WRITE_ALL(to_write);
	ASSERT_EQ(0, write_buffer(&ctx, &to_write, sizeof(to_write)));

	context_sync(&ctx);
	context_sync(&ctx);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_FAILED_REPLY);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);
}

/**
 * Sends a transaction to the context manager; before it replies, sends three
 * additional transactions from the same thread. Checks that the second one
 * fails with BR_FAILED_REPLY and that the third and forth ones are not
 * processed (i.e., the number of consumed bytes for the write operation is
 * zero).
 */
BINDER_TEST(transaction_3pending, server_empty_reply)
{
	struct context ctx;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 123,
	};

	ASSERT_WRITE_ALL(to_write);
	ASSERT_WRITE_ALL(to_write);
	ASSERT_EQ(0, write_buffer(&ctx, &to_write, sizeof(to_write)));
	ASSERT_EQ(0, write_buffer(&ctx, &to_write, sizeof(to_write)));

	context_sync(&ctx);
	context_sync(&ctx);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_FAILED_REPLY);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);
}

static void server_no_transaction(struct __test_metadata *_metadata,
				  size_t index, int comm_fd)
{
	struct context ctx;
	char data[256];

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);

	/* Wait for client to attempt to send transaction, if any. */

	context_sync(&ctx);

	/* Check that nothing arrived. */
	ASSERT_EQ(0, set_blocking(ctx.fd, false));
	ASSERT_EQ(-EAGAIN, read_no_alloc(&ctx, data, sizeof(data)));

	context_sync(&ctx);
}

/**
 * Acquires handle 0 from a non-manager process. It should work.
 */
BINDER_TEST(acquire_manager, server_no_transaction)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		uint32_t handle;
	} to_write = {
		.cmd = BC_ACQUIRE,
		.handle = 0,
	};

	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);
	context_sync(&ctx);
}

/**
 * Increfs handle 0 from a non-manager process. It should work.
 */
BINDER_TEST(increfs_manager, server_no_transaction)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		uint32_t handle;
	} to_write = {
		.cmd = BC_INCREFS,
		.handle = 0,
	};

	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);
	context_sync(&ctx);
}

/**
 * Tries to send handle 0. It should fail because it isn't initially populated.
 */
BINDER_TEST(send_manager_handle, server_no_transaction)
{
	struct context ctx;
	struct buffer buf;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	size_t offset = 0;
	struct flat_binder_object obj = {
		.hdr.type = BINDER_TYPE_HANDLE,
		.handle = 0,
		.cookie = 123456789,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_FAILED_REPLY);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);
}

static void server_receive_binder(struct __test_metadata *_metadata,
				  size_t index, int comm_fd, bool strong)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	{
		struct flat_binder_object obj = {
			.hdr.type = BINDER_TYPE_BINDER,
			.binder = 0xdeadbeef,
			.cookie = 0xc00f1e,
		};
		ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR_EXT, &obj);
	}

	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	ASSERT_NE(0, tr->data.ptr.buffer);
	ASSERT_NE(0, tr->data.ptr.offsets);
	ASSERT_EQ(sizeof(struct flat_binder_object), tr->data_size);
	ASSERT_EQ(sizeof(binder_size_t), tr->offsets_size);

	binder_size_t *offsets = (binder_size_t *)tr->data.ptr.offsets;
	ASSERT_EQ(0, offsets[0]);

	struct flat_binder_object *obj =
		(struct flat_binder_object *)tr->data.ptr.buffer;
	ASSERT_EQ(strong ? BINDER_TYPE_BINDER : BINDER_TYPE_WEAK_BINDER,
		  obj->hdr.type);
	ASSERT_EQ(0, obj->flags);
	ASSERT_EQ(0xdeadbeef, obj->binder);
	ASSERT_EQ(0xc00f1e, obj->cookie);

	trivial_reply(&ctx, tr);
	buffer_free(&buf);

	context_sync(&ctx);
}

static void server_receive_strong_binder(struct __test_metadata *_metadata,
					 size_t index, int comm_fd)
{
	server_receive_binder(_metadata, index, comm_fd, true);
}

static void server_receive_weak_binder(struct __test_metadata *_metadata,
				       size_t index, int comm_fd)
{
	server_receive_binder(_metadata, index, comm_fd, false);
}

static void client_send_manager(struct __test_metadata *_metadata,
				size_t index, int comm_fd,
				uint32_t obj_type, uint32_t cmd)
{
	struct context ctx;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	size_t offset = 0;
	struct flat_binder_object obj = {
		.hdr.type = obj_type,
		.handle = 0,
		.cookie = 123456789,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd0;
		uint32_t handle;
		uint32_t cmd1;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd0 = cmd,
		.handle = 0,
		.cmd1 = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);
}

/**
 * Creates a strong reference to the context manager by acquiring handle 0, then
 * sends this handle to the context manager. It should receive a binder.
 */
BINDER_TEST(send_manager_handle_after_acquire, server_receive_strong_binder)
{
	client_send_manager(_metadata, index, comm_fd,
			    BINDER_TYPE_HANDLE, BC_ACQUIRE);
}

/**
 * Creates a strong reference to the context manager by acquiring handle 0, then
 * sends this handle to the context manager as a weak handle. It should receive
 * a weak binder.
 */
BINDER_TEST(send_manager_weak_handle_after_acquire, server_receive_weak_binder)
{
	client_send_manager(_metadata, index, comm_fd,
			    BINDER_TYPE_WEAK_HANDLE, BC_ACQUIRE);
}

/**
 * Creates a weak reference to the context manager by increfing handle 0, then
 * sends this weak handle to the context manager. It should receive a weak
 * binder.
 */
BINDER_TEST(send_manager_weak_handle_after_increfs, server_receive_weak_binder)
{
	client_send_manager(_metadata, index, comm_fd,
			    BINDER_TYPE_WEAK_HANDLE, BC_INCREFS);
}

/**
 * Creates a weak reference to the context manager by increfing handle 0, then
 * sends this weak handle to the context manager as a strong handle. It should
 * fail because we cannot use "upgrade" a handle this way.
 */
BINDER_TEST(send_manager_handle_after_increfs, server_no_transaction)
{
	struct context ctx;
	struct buffer buf;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	size_t offset = 0;
	struct flat_binder_object obj = {
		.hdr.type = BINDER_TYPE_HANDLE,
		.handle = 0,
		.cookie = 123456789,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd0;
		uint32_t handle;
		uint32_t cmd1;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd0 = BC_INCREFS,
		.handle = 0,
		.cmd1 = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_FAILED_REPLY);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);
}

/**
 * Sends a transaction containing a file descriptor to the context manager, but
 * it isn't configured to accept file descriptors, so the transaction must fail.
 */
BINDER_TEST(transaction_fd_not_accepted, server_no_transaction)
{
	struct context ctx;
	struct buffer buf;
	int pipe_fds[2];

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	ASSERT_EQ(0, create_pipe(pipe_fds));

	size_t offset = 0;
	struct binder_fd_object obj = {
		.hdr.type = BINDER_TYPE_FD,
		.fd = pipe_fds[1],
		.cookie = 0x12345678,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_FAILED_REPLY);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);
}

static void server_receive_fd(struct __test_metadata *_metadata,
			      size_t index, int comm_fd)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	{
		struct flat_binder_object obj = {
			.hdr.type = BINDER_TYPE_BINDER,
			.flags = FLAT_BINDER_FLAG_ACCEPTS_FDS,
			.binder = 0xdeadbeef,
			.cookie = 0xc00f1e,
		};
		ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR_EXT, &obj);
	}

	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	ASSERT_NE(0, tr->data.ptr.buffer);
	ASSERT_NE(0, tr->data.ptr.offsets);
	ASSERT_EQ(sizeof(struct binder_fd_object), tr->data_size);
	ASSERT_EQ(sizeof(binder_size_t), tr->offsets_size);

	binder_size_t *offsets = (binder_size_t *)tr->data.ptr.offsets;
	ASSERT_EQ(0, offsets[0]);

	struct binder_fd_object *obj =
		(struct binder_fd_object *)tr->data.ptr.buffer;
	ASSERT_EQ(BINDER_TYPE_FD, obj->hdr.type);
	ASSERT_EQ(0, obj->pad_flags);
	ASSERT_EQ(0x12345678, obj->cookie);
	ASSERT_LE(0, obj->fd);

	context_sync(&ctx);

	/* Wait for peer to do something with fd before closing it. */

	context_sync(&ctx);

	close(obj->fd);

	trivial_reply(&ctx, tr);
	buffer_free(&buf);

	context_sync(&ctx);
}

/**
 * Sends a transaction containing a file descriptor to the context manager and
 * checks that it receives it.
 */
BINDER_TEST(transaction_send_fd, server_receive_fd)
{
	struct context ctx;
	struct buffer buf;
	int pipe_fds[2];
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	ASSERT_EQ(0, create_pipe(pipe_fds));

	size_t offset = 0;
	struct binder_fd_object obj = {
		.hdr.type = BINDER_TYPE_FD,
		.fd = pipe_fds[1],
		.cookie = 0x12345678,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);

	/* Close end of the pipe that was sent to peer. */
	close(pipe_fds[1]);

	/* Check that pipe remains 'alive' because peer has an fd to it. */
	char c;
	ASSERT_EQ(0, set_blocking(pipe_fds[0], false));
	ASSERT_EQ(-1, read(pipe_fds[0], &c, sizeof(c)));
	ASSERT_EQ(EAGAIN, errno);

	context_sync(&ctx);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	/* Now the pipe should be closed. */
	ASSERT_EQ(0, read(pipe_fds[0], &c, sizeof(c)));
	close(pipe_fds[0]);

	context_sync(&ctx);
}

static void server_fail_receive_fd(struct __test_metadata *_metadata,
				   size_t index, int comm_fd)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;
	struct epoll_event ev;
	char data[256];

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	{
		struct flat_binder_object obj = {
			.hdr.type = BINDER_TYPE_BINDER,
			.flags = FLAT_BINDER_FLAG_ACCEPTS_FDS,
			.binder = 0xdeadbeef,
			.cookie = 0xc00f1e,
		};
		ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR_EXT, &obj);
	}

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	/* Use up all file descriptors. */
	int epfd;
	int duped;
	ASSERT_LE(0, epfd = prepare_epoll(&ctx));

	ASSERT_NE(-1, duped = dup(epfd));
	while (dup(epfd) != -1);

	ASSERT_EQ(EMFILE, errno);

	context_sync(&ctx);

	/*
	 * Wait for "spurious" notification. It is in fact the transaction that
	 * is going to fail to be delivered.
	 */
	ASSERT_EQ(0, set_blocking(ctx.fd, false));
	ASSERT_NE(-1, epoll_wait(epfd, &ev, 1, 1000));
	ASSERT_EQ(-EAGAIN, read_no_alloc(&ctx, data, sizeof(data)));
	ASSERT_EQ(0, set_blocking(ctx.fd, true));

	/*
	 * Free up a file descriptor so that the next transaction containing a
	 * file descriptor can succeed.
	 */
	close(duped);

	context_sync(&ctx);

	/* Receive a file descriptor. */
	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	ASSERT_NE(0, tr->data.ptr.buffer);
	ASSERT_NE(0, tr->data.ptr.offsets);
	ASSERT_EQ(sizeof(struct binder_fd_object), tr->data_size);
	ASSERT_EQ(sizeof(binder_size_t), tr->offsets_size);

	binder_size_t *offsets = (binder_size_t *)tr->data.ptr.offsets;
	ASSERT_EQ(0, offsets[0]);

	struct binder_fd_object *obj =
		(struct binder_fd_object *)tr->data.ptr.buffer;
	ASSERT_EQ(BINDER_TYPE_FD, obj->hdr.type);
	ASSERT_EQ(0, obj->pad_flags);
	ASSERT_EQ(0x12345679, obj->cookie);
	ASSERT_LE(0, obj->fd);

	context_sync(&ctx);

	/* Wait for peer to do something with fd before closing it. */

	context_sync(&ctx);

	close(obj->fd);

	trivial_reply(&ctx, tr);
	buffer_free(&buf);

	context_sync(&ctx);
}

/**
 * Sends a transaction containing a file descriptor to the context manager that
 * has no file descriptors available. After freeing up one file descriptor slot,
 * sends the transaction again, at which point it must succeed.
 */
BINDER_TEST(transaction_fail_send_fd, server_fail_receive_fd)
{
	struct context ctx;
	struct buffer buf;
	int pipe_fds[2];
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	ASSERT_EQ(0, create_pipe(pipe_fds));

	size_t offset = 0;
	struct binder_fd_object obj = {
		.hdr.type = BINDER_TYPE_FD,
		.fd = pipe_fds[1],
		.cookie = 0x12345678,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	/* Write transaction that fails. */
	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_FAILED_REPLY);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);

	/* Write transaction again, this time it should succeed. */
	obj.cookie = 0x12345679;
	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);

	/* Close end of the pipe that was sent to peer. */
	close(pipe_fds[1]);

	/* Check that pipe remains 'alive' because peer has an fd to it. */
	char c;
	ASSERT_EQ(0, set_blocking(pipe_fds[0], false));
	ASSERT_EQ(-1, read(pipe_fds[0], &c, sizeof(c)));
	ASSERT_EQ(EAGAIN, errno);

	context_sync(&ctx);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	/* Now the pipe should be closed. */
	ASSERT_EQ(0, read(pipe_fds[0], &c, sizeof(c)));
	close(pipe_fds[0]);

	context_sync(&ctx);
}

static void server_fail_receive_2fds(struct __test_metadata *_metadata,
				     size_t index, int comm_fd)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;
	struct epoll_event ev;
	char data[256];

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	{
		struct flat_binder_object obj = {
			.hdr.type = BINDER_TYPE_BINDER,
			.flags = FLAT_BINDER_FLAG_ACCEPTS_FDS,
			.binder = 0xdeadbeef,
			.cookie = 0xc00f1e,
		};
		ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR_EXT, &obj);
	}

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	/* Use up all file descriptors, except one. */
	int epfd;
	int duped[2];
	ASSERT_LE(0, epfd = prepare_epoll(&ctx));

	ASSERT_NE(-1, duped[0] = dup(epfd));
	ASSERT_NE(-1, duped[1] = dup(epfd));
	while (dup(epfd) != -1);

	ASSERT_EQ(EMFILE, errno);

	close(duped[1]);

	context_sync(&ctx);

	/*
	 * Wait for "spurious" notification. It is in fact the transaction that
	 * is going to fail to be delivered.
	 */
	ASSERT_EQ(0, set_blocking(ctx.fd, false));
	ASSERT_NE(-1, epoll_wait(epfd, &ev, 1, 1000));
	ASSERT_EQ(-EAGAIN, read_no_alloc(&ctx, data, sizeof(data)));
	ASSERT_EQ(0, set_blocking(ctx.fd, true));

	/*
	 * Free up another file descriptor so that the next transaction
	 * containing two file descriptors can succeed.
	 */
	close(duped[0]);

	context_sync(&ctx);

	/* Receive two file descriptors. */
	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	ASSERT_NE(0, tr->data.ptr.buffer);
	ASSERT_NE(0, tr->data.ptr.offsets);
	ASSERT_EQ(2 * sizeof(struct binder_fd_object), tr->data_size);
	ASSERT_EQ(2 * sizeof(binder_size_t), tr->offsets_size);

	binder_size_t *offsets = (binder_size_t *)tr->data.ptr.offsets;
	ASSERT_EQ(0, offsets[0]);
	ASSERT_EQ(sizeof(struct binder_fd_object), offsets[1]);

	struct binder_fd_object *obj =
		(struct binder_fd_object *)tr->data.ptr.buffer;
	ASSERT_EQ(BINDER_TYPE_FD, obj[0].hdr.type);
	ASSERT_EQ(0, obj[0].pad_flags);
	ASSERT_EQ(0x1234567a, obj[0].cookie);
	ASSERT_LE(0, obj[0].fd);

	ASSERT_EQ(BINDER_TYPE_FD, obj[1].hdr.type);
	ASSERT_EQ(0, obj[1].pad_flags);
	ASSERT_EQ(0x1234567b, obj[1].cookie);
	ASSERT_LE(0, obj[1].fd);

	context_sync(&ctx);

	/* Wait for peer to do something with fd before closing it. */

	context_sync(&ctx);

	close(obj[0].fd);
	close(obj[1].fd);

	trivial_reply(&ctx, tr);
	buffer_free(&buf);

	context_sync(&ctx);
}

/**
 * Sends a transaction containing two file descriptors to the context manager
 * that only has one available file descriptor, so the request must fail. Once
 * the manager frees up another file descriptor, sends the transaction again and
 * it must succeed.
 */
BINDER_TEST(transaction_fail_send_2fds, server_fail_receive_2fds)
{
	struct context ctx;
	struct buffer buf;
	int pipe_fds[4];
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	ASSERT_EQ(0, create_pipe(pipe_fds));
	ASSERT_EQ(0, create_pipe(pipe_fds + 2));

	size_t offset[2] = { 0, sizeof(struct binder_fd_object) };
	struct binder_fd_object obj[] = {
		{
			.hdr.type = BINDER_TYPE_FD,
			.fd = pipe_fds[1],
			.cookie = 0x12345678,
		},
		{
			.hdr.type = BINDER_TYPE_FD,
			.fd = pipe_fds[3],
			.cookie = 0x12345679,
		},
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	/* Write transaction that fails. */
	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_FAILED_REPLY);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);

	/* Write transaction again, this time it should succeed. */
	obj[0].cookie = 0x1234567a;
	obj[1].cookie = 0x1234567b;
	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);

	/* Close end of the pipes that were sent to peer. */
	close(pipe_fds[1]);
	close(pipe_fds[3]);

	/* Check that pipes remain 'alive' because peer has fds to them. */
	char c;
	ASSERT_EQ(0, set_blocking(pipe_fds[0], false));
	ASSERT_EQ(-1, read(pipe_fds[0], &c, sizeof(c)));
	ASSERT_EQ(EAGAIN, errno);

	ASSERT_EQ(0, set_blocking(pipe_fds[2], false));
	ASSERT_EQ(-1, read(pipe_fds[2], &c, sizeof(c)));
	ASSERT_EQ(EAGAIN, errno);

	context_sync(&ctx);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	/* Now the pipes should be closed. */
	ASSERT_EQ(0, read(pipe_fds[0], &c, sizeof(c)));
	close(pipe_fds[0]);

	ASSERT_EQ(0, read(pipe_fds[2], &c, sizeof(c)));
	close(pipe_fds[2]);

	context_sync(&ctx);
}

static void server_reply_with_fd(struct __test_metadata *_metadata,
				 size_t index, int comm_fd)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;
	int pipe_fds[2];

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	/* Get transaction. */
	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	/* Prepare reply with FD in it. */
	ASSERT_EQ(0, create_pipe(pipe_fds));

	size_t offset = 0;
	struct binder_fd_object obj = {
		.hdr.type = BINDER_TYPE_FD,
		.fd = pipe_fds[1],
		.cookie = 0x12345678,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd0;
		size_t ptr;
		uint32_t cmd1;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd0 = BC_FREE_BUFFER,
		.ptr = tr->data.ptr.buffer,
		.cmd1 = BC_REPLY,
		.tr.code = tr->code + 1,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};
	buffer_free(&buf);

	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 512);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);

	/* Close end of the pipe that was sent to peer. */
	close(pipe_fds[1]);

	/* Check that pipe remains 'alive' because peer has an fd to it. */
	char c;
	ASSERT_EQ(0, set_blocking(pipe_fds[0], false));
	ASSERT_EQ(-1, read(pipe_fds[0], &c, sizeof(c)));
	ASSERT_EQ(EAGAIN, errno);

	context_sync(&ctx);

	/* Let peer close the file descriptor. */

	context_sync(&ctx);

	/* Now the pipe should be closed. */
	ASSERT_EQ(0, read(pipe_fds[0], &c, sizeof(c)));
	close(pipe_fds[0]);
}

/**
 * Sends a file descriptor in a reply to a transaction.
 */
BINDER_TEST(receive_fd_in_reply, server_reply_with_fd)
{
	struct context ctx;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 123,
		.tr.flags = TF_ACCEPT_FDS,
	};

	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);

	ASSERT_NE(0, tr->data.ptr.buffer);
	ASSERT_NE(0, tr->data.ptr.offsets);
	ASSERT_EQ(sizeof(struct binder_fd_object), tr->data_size);
	ASSERT_EQ(sizeof(binder_size_t), tr->offsets_size);

	binder_size_t *offsets = (binder_size_t *)tr->data.ptr.offsets;
	ASSERT_EQ(0, offsets[0]);

	struct binder_fd_object *obj =
		(struct binder_fd_object *)tr->data.ptr.buffer;
	ASSERT_EQ(BINDER_TYPE_FD, obj->hdr.type);
	ASSERT_EQ(0, obj->pad_flags);
	ASSERT_EQ(0x12345678, obj->cookie);
	ASSERT_LE(0, obj->fd);

	context_sync(&ctx);

	/* Peer is checking that we're holding the fd opened. */

	context_sync(&ctx);

	close(obj->fd);

	context_sync(&ctx);
}

static void server_fail_reply_with_fd(struct __test_metadata *_metadata,
				      size_t index, int comm_fd)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;
	int pipe_fds[2];

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	/* Get transaction. */
	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	/* Prepare reply with FD in it. */
	ASSERT_EQ(0, create_pipe(pipe_fds));

	size_t offset = 0;
	struct binder_fd_object obj = {
		.hdr.type = BINDER_TYPE_FD,
		.fd = pipe_fds[1],
		.cookie = 0x12345678,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd0;
		size_t ptr;
		uint32_t cmd1;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd0 = BC_FREE_BUFFER,
		.ptr = tr->data.ptr.buffer,
		.cmd1 = BC_REPLY,
		.tr.code = tr->code + 1,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};
	buffer_free(&buf);

	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 512);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);

	/* Close end of the pipe that we failed to send to peer. */
	close(pipe_fds[1]);

	/*
	 * The other end should indicate EOF because noone else should be
	 * holding the pipe open.
	 */
	char c;
	ASSERT_EQ(0, read(pipe_fds[0], &c, sizeof(c)));
	close(pipe_fds[0]);

	context_sync(&ctx);
}

/**
 * Sends a file descriptor in a reply to a transaction that doesn't have
 * TF_ACCEPT_FDS in its flags, so the reply must be rejected.
 */
BINDER_TEST(fail_receive_fd_in_reply, server_fail_reply_with_fd)
{
	struct context ctx;
	struct buffer buf;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 123,
	};

	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_FAILED_REPLY);
	ASSERT_BUFFER_EMPTY(&buf);

	context_sync(&ctx);

	/* Peer is checking that we're not holding the fd opened. */

	context_sync(&ctx);
}

static void server_receive_handle(struct __test_metadata *_metadata,
				  size_t index, int comm_fd, bool strong,
				  bool incref, bool acquire, bool free_buffer)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	ASSERT_NE(0, tr->data.ptr.buffer);
	ASSERT_NE(0, tr->data.ptr.offsets);
	ASSERT_EQ(sizeof(struct flat_binder_object), tr->data_size);
	ASSERT_EQ(sizeof(binder_size_t), tr->offsets_size);

	binder_size_t *offsets = (binder_size_t *)tr->data.ptr.offsets;
	ASSERT_EQ(0, offsets[0]);

	struct flat_binder_object *obj =
		(struct flat_binder_object *)tr->data.ptr.buffer;
	ASSERT_EQ(strong ? BINDER_TYPE_HANDLE : BINDER_TYPE_WEAK_HANDLE,
		  obj->hdr.type);
	ASSERT_EQ(0, obj->flags);
	ASSERT_EQ(1, obj->handle);
	ASSERT_EQ(0, obj->cookie);

	if (incref) {
		struct __attribute__((__packed__)) {
			uint32_t cmd;
			uint32_t handle;
		} to_write = {
			.cmd = BC_INCREFS,
			.handle = obj->handle,
		};
		ASSERT_WRITE_ALL(to_write);
	}

	if (acquire) {
		struct __attribute__((__packed__)) {
			uint32_t cmd;
			uint32_t handle;
		} to_write = {
			.cmd = BC_ACQUIRE,
			.handle = obj->handle,
		};
		ASSERT_WRITE_ALL(to_write);
	}

	if (free_buffer) {
		struct __attribute__((__packed__)) {
			uint32_t cmd;
			size_t ptr;
		} to_write = {
			.cmd = BC_FREE_BUFFER,
			.ptr = tr->data.ptr.buffer,
		};
		ASSERT_WRITE_ALL(to_write);
	}

	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_REPLY,
		.tr.code = tr->code + 1,
	};
	buffer_free(&buf);
	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);
}

static void server_receive_strong_handle(struct __test_metadata *_metadata,
					 size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, true,
			      false, false, true);
}

static void server_recv_acquire_strong_handle(struct __test_metadata *_metadata,
					      size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, true,
			      false, true, true);
}

static void server_recv_incref_strong_handle(struct __test_metadata *_metadata,
					      size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, true,
			      true, false, true);
}

static void server_recv_acquire_incref_strong_handle(
		struct __test_metadata *_metadata, size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, true,
			      true, true, true);
}

static void server_receive_weak_handle(struct __test_metadata *_metadata,
				       size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, false,
			      false, false, true);
}

static void server_recv_acquire_weak_handle(struct __test_metadata *_metadata,
					    size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, false,
			      false, true, true);
}

static void server_recv_increfs_weak_handle(struct __test_metadata *_metadata,
					    size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, false,
			      true, false, true);
}

static void server_recv_strong_handle_nofree(struct __test_metadata *_metadata,
					     size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, true,
			      false, false, false);
}

static void server_recv_weak_handle_nofree(struct __test_metadata *_metadata,
					   size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, false,
			      false, false, false);
}

static void server_recv_acquire_weak_handle_nofree(
		struct __test_metadata *_metadata, size_t index, int comm_fd)
{
	server_receive_handle(_metadata, index, comm_fd, false,
			      false, true, false);
}

static void client_send_binder(struct __test_metadata *_metadata,
			       size_t index, int comm_fd, bool strong,
			       bool expect_increfs, bool expect_acquires)
{
	struct context ctx;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	size_t offset = 0;
	struct flat_binder_object obj = {
		.hdr.type =
			strong ? BINDER_TYPE_BINDER : BINDER_TYPE_WEAK_BINDER,
		.binder = 987654321,
		.cookie = 123456789,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);

	if (expect_increfs) {
		ASSERT_BUFFER_EQ(&buf, uint32_t, BR_INCREFS);
		ASSERT_BUFFER_EQ(&buf, binder_uintptr_t, 987654321);
		ASSERT_BUFFER_EQ(&buf, binder_uintptr_t, 123456789);
	}

	if (expect_acquires) {
		ASSERT_BUFFER_EQ(&buf, uint32_t, BR_ACQUIRE);
		ASSERT_BUFFER_EQ(&buf, binder_uintptr_t, 987654321);
		ASSERT_BUFFER_EQ(&buf, binder_uintptr_t, 123456789);
	}

	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);
}

/**
 * Sends a transaction containing a binder object to the context manager and
 * checks that it receives a handle to it.
 */
BINDER_TEST(transaction_send_binder, server_receive_strong_handle)
{
	client_send_binder(_metadata, index, comm_fd, true, false, false);
}

/**
 * Sends a transaction containing a binder object to the context manager and
 * checks that it receives a handle to it. The recipient acquires a reference to
 * the object before freeing the buffer, so the client must see acquire and
 * increfs requests.
 */
BINDER_TEST(transaction_send_binder_acquire, server_recv_acquire_strong_handle)
{
	client_send_binder(_metadata, index, comm_fd, true, true, true);
}

/**
 * Sends a transaction containing a binder object to the context manager and
 * checks that it receives a handle to it. The recipient increments the weak ref
 * count of the object before freeing the buffer, so the client must see an
 * increfs request.
 */
BINDER_TEST(transaction_send_binder_incref, server_recv_incref_strong_handle)
{
	client_send_binder(_metadata, index, comm_fd, true, true, false);
}

/**
 * Sends a transaction containing a binder object to the context manager and
 * checks that it receives a handle to it. The recipient acquires a reference
 * and increments the weak ref count of the object before freeing the buffer, so
 * the client must see acquire and increfs requests.
 */
BINDER_TEST(transaction_send_binder_acquire_incref,
	    server_recv_acquire_incref_strong_handle)
{
	client_send_binder(_metadata, index, comm_fd, true, true, true);
}

/**
 * Sends a transaction containing a weak binder object to the context manager
 * and checks that it receives a weak handle to it.
 */
BINDER_TEST(transaction_send_weak_binder, server_receive_weak_handle)
{
	client_send_binder(_metadata, index, comm_fd, false, false, false);
}

/**
 * Sends a transaction containing a weak binder object to the context manager
 * and checks that it receives a weak handle to it. The recipient tries to
 * acquire a reference to the object, but since this isn't allowed, the client
 * won't see any acquire or increfs.
 */
BINDER_TEST(transaction_send_weak_binder_acquire,
	    server_recv_acquire_weak_handle)
{
	client_send_binder(_metadata, index, comm_fd, false, false, false);
}

/**
 * Sends a transaction containing a weak binder object to the context manager
 * and checks that it receives a weak handle to it. The recipient increments the
 * weak ref count of the object before freeing the buffer, so the client must
 * see an increfs request.
 */
BINDER_TEST(transaction_send_weak_binder_incref,
	    server_recv_increfs_weak_handle)
{
	client_send_binder(_metadata, index, comm_fd, false, true, false);
}

/**
 * Sends a transaction containing a binder object to the context manager and
 * checks that it receives a handle to it. The server does not free the buffer,
 * so the client gets INCREFS and ACQUIRE for the binder that is still alive.
 */
BINDER_TEST(transaction_send_binder_nofree, server_recv_strong_handle_nofree)
{
	client_send_binder(_metadata, index, comm_fd, true, true, true);
}

/**
 * Sends a transaction containing a weak binder object to the context manager
 * and checks that it receives a weak handle to it. The server does not free the
 * buffer, so the client gets an INCREFS for the binder that is still alive.
 */
BINDER_TEST(transaction_send_weak_binder_nofree, server_recv_weak_handle_nofree)
{
	client_send_binder(_metadata, index, comm_fd, false, true, false);
}

/**
 * Sends a transaction containing a weak binder object to the context manager
 * and checks that it receives a weak handle to it. The recipient tries to
 * acquire a reference to the object and doesn't free the buffer.  Since
 * acquiring is not allowed, the client only sees an incref because it hasn't
 * freed the buffer.
 */
BINDER_TEST(transaction_send_weak_binder_acquire_nofree,
	    server_recv_acquire_weak_handle_nofree)
{
	client_send_binder(_metadata, index, comm_fd, false, true, false);
}

static void server_inline_callback(struct __test_metadata *_metadata,
				   size_t index, int comm_fd)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	/* Receive a transaction from the client. */
	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	ASSERT_NE(0, tr->data.ptr.buffer);
	ASSERT_NE(0, tr->data.ptr.offsets);
	ASSERT_EQ(sizeof(struct flat_binder_object), tr->data_size);
	ASSERT_EQ(sizeof(binder_size_t), tr->offsets_size);

	binder_size_t *offsets = (binder_size_t *)tr->data.ptr.offsets;
	ASSERT_EQ(0, offsets[0]);

	struct flat_binder_object *obj =
		(struct flat_binder_object *)tr->data.ptr.buffer;
	ASSERT_EQ(BINDER_TYPE_HANDLE, obj->hdr.type);
	ASSERT_EQ(0, obj->flags);
	ASSERT_EQ(1, obj->handle);
	ASSERT_EQ(0, obj->cookie);

	/* Call the client back and receive reply. */
	trivial_transaction(&ctx, 1, 125);

	/* Reply to the original request. */
	trivial_reply(&ctx, tr);
	buffer_free(&buf);

	context_sync(&ctx);
}

/**
 * Sends a binder object from one process to another, recipient then uses the
 * object to call the original sender before replying to the original
 * transaction.
 */
BINDER_TEST(inline_callback, server_inline_callback)
{
	struct context ctx;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	/*
	 * Send transaction to the server, and get a transaction (instead of a
	 * reply) from it.
	 */
	size_t offset = 0;
	struct flat_binder_object obj = {
		.hdr.type = BINDER_TYPE_BINDER,
		.binder = 987654321,
		.cookie = 123456789,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	buf = write_read_buffer(&ctx, &to_write, sizeof(to_write), 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_INCREFS);
	ASSERT_BUFFER_EQ(&buf, binder_uintptr_t, 987654321);
	ASSERT_BUFFER_EQ(&buf, binder_uintptr_t, 123456789);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_ACQUIRE);
	ASSERT_BUFFER_EQ(&buf, binder_uintptr_t, 987654321);
	ASSERT_BUFFER_EQ(&buf, binder_uintptr_t, 123456789);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION_COMPLETE);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(987654321, tr->target.ptr);
	ASSERT_EQ(123456789, tr->cookie);
	ASSERT_EQ(125, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);

	/* Reply to inline transaction. */
	trivial_reply(&ctx, tr);
	buffer_free(&buf);

	/* Receive reply to original transaction. */
	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_REPLY);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_EQ(124, tr->code);
	ASSERT_BUFFER_EMPTY(&buf);
	buffer_free(&buf);

	context_sync(&ctx);
}

static void server_callback_fails_dead(struct __test_metadata *_metadata,
				       size_t index, int comm_fd)
{
	struct context ctx;
	uint32_t cmd;
	struct buffer buf;
	struct binder_transaction_data *tr;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	/* Receive a transaction from the client. */
	buf = read_buffer(&ctx, 1024);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_NOOP);
	ASSERT_BUFFER_EQ(&buf, uint32_t, BR_TRANSACTION);
	tr = ASSERT_BUFFER_ADVANCE(&buf, sizeof(*tr));
	ASSERT_BUFFER_EMPTY(&buf);

	ASSERT_NE(0, tr->data.ptr.buffer);
	ASSERT_NE(0, tr->data.ptr.offsets);
	ASSERT_EQ(sizeof(struct flat_binder_object), tr->data_size);
	ASSERT_EQ(sizeof(binder_size_t), tr->offsets_size);

	binder_size_t *offsets = (binder_size_t *)tr->data.ptr.offsets;
	ASSERT_EQ(0, offsets[0]);

	struct flat_binder_object *obj =
		(struct flat_binder_object *)tr->data.ptr.buffer;
	ASSERT_EQ(BINDER_TYPE_HANDLE, obj->hdr.type);
	ASSERT_EQ(0, obj->flags);
	ASSERT_EQ(1, obj->handle);
	ASSERT_EQ(0, obj->cookie);

	/* Call the client back and receive reply. */
	trivial_transaction_dead_server(&ctx, obj->handle, 125);

	context_sync(&ctx);
}

/**
 * Sends a binder object from one process to another, recipient then uses the
 * object to call the original sender before replying to the original
 * transaction. Exits process (close handle and unmap map) while callback is
 * queued, then checks that the server receives an error.
 */
BINDER_TEST(process_exits_with_callback_queued_to_thread,
	    server_callback_fails_dead)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	/* Send transaction containing a binder to the server. */
	size_t offset = 0;
	struct flat_binder_object obj = {
		.hdr.type = BINDER_TYPE_BINDER,
		.binder = 987654321,
		.cookie = 123456789,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);

	/* Exit process now that inline callback is queued. */
	close(ctx.fd);
	munmap(ctx.shared_ptr, ctx.size);

	context_sync(&ctx);
}

/**
 * Sends a binder object from one process to another, recipient then uses the
 * object to call the original sender before replying to the original
 * transaction. Exits the thread while callback is queued, then checks that the
 * server receives an error.
 */
BINDER_TEST(thread_exits_with_callback_queued, server_callback_fails_dead)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	/* Send transaction containing a binder to the server. */
	size_t offset = 0;
	struct flat_binder_object obj = {
		.hdr.type = BINDER_TYPE_BINDER,
		.binder = 987654321,
		.cookie = 123456789,
	};
	struct __attribute__((__packed__)) {
		uint32_t cmd;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd = BC_TRANSACTION,
		.tr.code = 123,
		.tr.data.ptr.buffer = (binder_uintptr_t)&obj,
		.tr.data_size = sizeof(obj),
		.tr.data.ptr.offsets = (binder_uintptr_t)&offset,
		.tr.offsets_size = sizeof(offset),
	};

	ASSERT_WRITE_ALL(to_write);

	context_sync(&ctx);

	/* Exit thread now that inline callback is queued. */
	ioctl_no_failure(ctx.fd, BINDER_THREAD_EXIT, NULL);

	context_sync(&ctx);
}

static void client_send_transactions(struct __test_metadata *_metadata,
				     size_t index, int comm_fd)
{
	struct context ctx;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);

	context_sync(&ctx);

	/* Send first transaction. */
	trivial_transaction(&ctx, 0, 123);
	trivial_transaction(&ctx, 0, 125);

	/* Send third transaction after synchronising. */
	context_sync(&ctx);
	trivial_transaction(&ctx, 0, 127);

	/* Send fourth transaction. */
	trivial_transaction(&ctx, 0, 129);

	/* Send fifth transaction after synchronising. */
	context_sync(&ctx);
	trivial_transaction(&ctx, 0, 131);

	context_sync(&ctx);
}

void *looper(void *arg)
{
	struct context *ctx = arg;
	struct __test_metadata *_metadata = ctx->_metadata;
	uint32_t cmd;

	cmd = BC_REGISTER_LOOPER;
	ASSERT_EQ(sizeof(cmd), write_buffer(ctx, &cmd, sizeof(cmd)));

	return NULL;
}

/**
 * Server sets the number of threads to 2 and receives transactions from clients
 * so as to trigger the request of new threads.
 */
BINDER_TEST(max_threads, client_send_transactions)
{
	struct context ctx;
	uint32_t cmd;

	context_init(&ctx, comm_fd, default_mapped_size, index, _metadata);
	ioctl_no_failure(ctx.fd, BINDER_SET_CONTEXT_MGR, NULL);

	{
		uint32_t v = 2;
		ioctl_no_failure(ctx.fd, BINDER_SET_MAX_THREADS, &v);
	}

	context_sync(&ctx);

	cmd = BC_ENTER_LOOPER;
	ASSERT_WRITE_ALL(cmd);

	/* Get the first transaction. */
	trivial_receive_reply(&ctx, true);

	/*
	 * Get the second transaction, here we don't get a SPAWN request because
	 * the previous one is still pending.
	 */
	trivial_receive_reply(&ctx, false);

	/* Spawn looper thread that registers with binder then exits. */
	pthread_t thread;
	ASSERT_EQ(0, pthread_create(&thread, NULL, looper, &ctx));
	ASSERT_EQ(0, pthread_join(thread, NULL));

	context_sync(&ctx);

	/*
	 * Get the third transaction. We should get another SPAWN given that the
	 * other thread has spawned and isn't waiting for requests.
	 */
	trivial_receive_reply(&ctx, true);

	/*
	 * Get the fourth transaction, here we don't get a SPAWN request because
	 * the previous one is still pending.
	 */
	trivial_receive_reply(&ctx, false);

	/* Spawn looper thread that registers with binder then exits. */
	ASSERT_EQ(0, pthread_create(&thread, NULL, looper, &ctx));
	ASSERT_EQ(0, pthread_join(thread, NULL));

	context_sync(&ctx);

	/*
	 * Get the fifth transaction, here we don't get a SPAWN request because
	 * we have reached the limit.
	 */
	trivial_receive_reply(&ctx, false);

	context_sync(&ctx);
}


/* TODO: Add test case of transaction with bad object type. */
TEST_HARNESS_MAIN
