#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdalign.h>
#include <time.h>

#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <linux/ioctl.h>
#include <linux/android/binder.h>

static size_t handle_read(int fd, struct binder_write_read *b)
{
	char *ptr = (char *)b->read_buffer;
	char *limit = ptr + b->read_consumed;
	struct binder_transaction_data *tr;
	size_t ret = 0;

	while (limit - ptr >= sizeof(uint32_t)) {
		uint32_t v = *(uint32_t *)ptr;
		ptr += sizeof(uint32_t);
		switch (v) {
		case BR_REPLY:
			tr = (struct binder_transaction_data *)ptr;
			ptr += sizeof(*tr);
			if (ptr > limit) {
				printf("Truncated transaction.\n");
				break;
			}
			ret = tr->data.ptr.buffer;
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

	return ret;
}

int main(int argc, char **argv)
{
	int ret;
	size_t i;
	struct timespec begin, end;

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

	uint32_t buf[512];
	static struct __attribute__((__packed__)) {
		uint32_t cmd0;
		size_t addr;
		uint32_t cmd1;
		struct binder_transaction_data tr;
	} to_write = {
		.cmd0 = BC_FREE_BUFFER,
		.addr = 0,
		.cmd1 = BC_TRANSACTION,
		.tr.target.handle = 0,
		.tr.code = 0,
	};
	struct binder_write_read b = {
		.write_buffer = (size_t)&to_write,
		.write_size = sizeof(to_write),
		.read_buffer = (size_t)&buf[0],
		.read_size = sizeof(buf),
	};
	ret = ioctl(fd, BINDER_WRITE_READ, &b);
	if (ret == -1) {
		perror("ioctl");
		return 1;
	}

	to_write.addr = handle_read(fd, &b);

	clock_gettime(CLOCK_MONOTONIC, &begin);
	for (i = 0; i < 1000000; i++) {
		b.read_consumed = 0;
		b.write_consumed = 0;
		ret = ioctl(fd, BINDER_WRITE_READ, &b);
		if (ret == -1) {
			perror("ioctl");
			return 1;
		}
		to_write.addr = handle_read(fd, &b);
	}
	clock_gettime(CLOCK_MONOTONIC, &end);

	end.tv_sec -= begin.tv_sec;
	if (begin.tv_nsec > end.tv_nsec) {
		end.tv_sec--;
		end.tv_nsec += 1000000000;
	}
	end.tv_nsec -= begin.tv_nsec;
	printf("Total time: %lld.%.9ld\n", (long long)end.tv_sec, end.tv_nsec);

	close(fd);

	return 0;
}
