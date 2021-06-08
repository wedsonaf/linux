#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdalign.h>

#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <linux/ioctl.h>
#include <linux/android/binder.h>

static void handle_read(int fd, struct binder_write_read* b)
{
	static struct __attribute__((__packed__)) {
		uint32_t cmd0;
		size_t ptr;
		uint32_t cmd1;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd0 = BC_FREE_BUFFER,
		.cmd1 = BC_REPLY,
		.tr.target.handle = 0,
		.tr.code = 0,
	};
	char *ptr = (char *)b->read_buffer;
	char *limit = ptr + b->read_consumed;
	struct binder_transaction_data *tr;

	while (limit - ptr >= sizeof(uint32_t)) {
		uint32_t v = *(uint32_t *)ptr;
		ptr += sizeof(uint32_t);
		switch (v) {
		case BR_TRANSACTION:
			tr = (struct binder_transaction_data *)ptr;
			ptr += sizeof(*tr);
			if (ptr > limit) {
				printf("Truncated transaction.\n");
				break;
			}

			to_write.ptr = tr->data.ptr.buffer;
			b->write_buffer = (size_t)&to_write;
			b->write_size = sizeof(to_write);
			b->write_consumed = 0;
			break;

		case BR_NOOP:
			break;

		case BR_TRANSACTION_COMPLETE:
			break;

		default:
			printf("Unknown reply: 0x%x\n", v);
			ptr = limit;
		}
	}
}

int main(int argc, char **argv)
{
	int ret;

	if (argc != 2) {
		fprintf(stderr, "Usage: %s <binder-file-name>\n", argv[0]);
		return 1;
	}

	int fd = open(argv[1], O_RDWR);
	if (fd == -1) {
		perror("open");
		return 1;
	}

	void *shared_ptr = mmap(NULL, 4096, PROT_READ, MAP_PRIVATE, fd, 0);
	if (shared_ptr == MAP_FAILED) {
		perror("mmap");
		return 1;
	}

	ret = ioctl(fd, BINDER_SET_CONTEXT_MGR, NULL);
	if (ret == -1) {
		perror("ioctl");
		return 1;
	}

	{
		uint32_t cmd = BC_ENTER_LOOPER;
		struct binder_write_read b = {
			.write_buffer = (size_t)&cmd,
			.write_size = sizeof(cmd),
		};
		int ret = ioctl(fd, BINDER_WRITE_READ, &b);
		if (ret == -1) {
			perror("ioctl(BC_ENTER_LOOPER)");
		}
	}

	uint32_t buf[512];
	struct binder_write_read b = {
		.read_buffer = (size_t)&buf[0],
		.read_size = sizeof(buf),
	};
	for (;;) {
		b.read_consumed = 0;
		ret = ioctl(fd, BINDER_WRITE_READ, &b);
		if (ret == -1) {
			perror("ioctl");
			continue;
		}

		handle_read(fd, &b);
	}

	close(fd);

	return 0;
}
