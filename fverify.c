/*
 * fverify - yet another tool for files verification
 *
 * Copyright (C) 2014 Roman Pen <r.peniaev@gmail.com>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License version 2 as
 *  published by the Free Software Foundation.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 */

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <ftw.h>
#include <getopt.h>
#include <limits.h>
#include <malloc.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#define MAX_OPENED 256
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))
#define __round_mask(x, y) ((__typeof__(x))((y)-1))
#define round_up(x, y) ((((x)-1) | __round_mask(x, y))+1)
#define round_down(x, y) ((x) & ~__round_mask(x, y))

/* Common arguments */
const char   *arg_dir_name = NULL;
const char   *arg_file_name = "fverify.list";
int           arg_quiet = 0;

/* Generate arguments */
unsigned int arg_opened = 1;
unsigned int arg_odirect;
unsigned int arg_mmap;
unsigned int arg_min_block_size;
unsigned int arg_max_block_size;
unsigned int arg_io_seq = 100;
unsigned int arg_shuffle;
int          *arg_seed;

/* Verify arguments */
int          arg_skip_prefix = 0;

#define OPEN_CMD  "open"
#define STAT_CMD  "stat"
#define READ_CMD  "read"
#define MMAP_CMD  "mmap"
#define CLOSE_CMD "close"

struct verif_stat {
	unsigned int reads;
	unsigned int mmaps;
	unsigned int cached;
	unsigned int odirects;
	unsigned long long msecs;
	unsigned long long bytes;

	unsigned int err_reads;
	unsigned int err_mmaps;
	unsigned int err_stats;
};

struct verif_stat global_stat;

static uint32_t crc32_table[256];
static int crc32_inited;

static inline void crc32_init(void)
{
	const uint32_t poly = 0xEDB88320;

	uint32_t i;
	uint32_t j;
	uint32_t r;

	for (i = 0; i < 256; ++i) {
		r = i;
		for (j = 0; j < 8; ++j)
			r = (r >> 1) ^ (poly & ~((r & 1) - 1));

		crc32_table[i] = r;
	}

	return;
}

static inline uint32_t crc32(const uint8_t *buf, size_t size, uint32_t crc)
{
	if (!crc32_inited) {
		crc32_inited = 1;
		crc32_init();
	}

	crc = ~crc;

	while (size != 0) {
		crc = crc32_table[*buf++ ^ (crc & 0xFF)] ^ (crc >> 8);
		--size;
	}

	return ~crc;
}

static inline unsigned long long msecs_epoch()
{
	struct timeval tv;
	gettimeofday(&tv, NULL);
	return ((unsigned long long)tv.tv_sec * 1000) +
		((unsigned long long)tv.tv_usec / 1000);
}


static inline void progress(const char *msg,
			    unsigned long long x,
			    unsigned long long n)
{
	static unsigned long long last_visit;
	static unsigned int calls;
	unsigned long long now = msecs_epoch();
	const char ch_list[] = {'|', '/', '-', '\\'};
	char ch;
	double ratio;

	/* Keep silence */
	if (arg_quiet)
		return;
	if (last_visit && now - last_visit < 100)
		return;
	last_visit = now;

	ch = ch_list[calls++ % sizeof(ch_list)];

	ratio = (double)x/n;

	printf("%3d%% ", (int)(ratio*100));

	/* ANSI Control codes to go back to the previous line and clear it. */
	printf("%s %c\n\033[F\033[J", msg, ch);
}

static ssize_t do_fread(void *buf, size_t nbyte, FILE *f)
{
	ssize_t ret = 0, r;
	do {
		r = fread(buf + ret, 1, nbyte - ret, f);
		if (r > 0)
			ret += r;
	} while (r > 0 && (size_t)ret != nbyte);

	return ret;
}

static inline unsigned int rand_between(unsigned int M, unsigned int N)
{
	return M + (int)((double)rand() /
			 (((double)RAND_MAX + 1) / (N - M + 1)));
}

struct bitset {
	size_t sz;
	uint32_t bits[];
};

static inline struct bitset *bitset_alloc(size_t size)
{
	struct bitset *bitset;
	const unsigned int bits = sizeof(bitset->bits[0]) * 8;
	size_t full_size;
	if (!size)
		return NULL;
	size = (size + bits - 1) / bits;
	full_size = sizeof(struct bitset) + sizeof(bitset->bits[0]) * size;

	bitset = malloc(full_size);
	if (!bitset)
		return NULL;
	memset(bitset, 0, full_size);
	bitset->sz = size;
	return bitset;
}

static inline void bitset_free(struct bitset *bitset)
{
	free(bitset);
}

static inline int bitset_fcb(struct bitset *bitset)
{
	unsigned int i;
	const unsigned int bits = sizeof(bitset->bits[0]) * 8;

	if (!bitset)
		return -1;
	for (i = 0; i < bitset->sz; ++i) {
		uint32_t x = bitset->bits[i];
		uint32_t t = 0;
		while (t < bits && (x & (1 << t)) != 0)
			t++;
		if (t == bits)
			continue;
		return i * bits + t;
	}
	return -1;
}

static inline void bitset_set(struct bitset *bitset, unsigned int bit)
{
	const unsigned int bits = sizeof(bitset->bits[0]) * 8;
	unsigned int i = bit / bits;
	bit &= bits - 1;
	bitset->bits[i] |= (1 << bit);
}

static inline void bitset_clear(struct bitset *bitset, unsigned int bit)
{
	const unsigned int bits = sizeof(bitset->bits[0]) * 8;
	unsigned int i = bit / bits;
	bit &= bits - 1;
	bitset->bits[i] &= ~(1 << bit);
}

enum wfq_state {
	wfq_active = 0,
	wfq_inactive,
	wfq_repeat
};

struct wfq_queue {
	unsigned int    priority;
	unsigned int    runcount;
	enum wfq_state (*queue_fn)(struct wfq_queue *);
	void            *queue_arg;
};

static inline float wfq_get_finish_time(const struct wfq_queue *q)
{
	float prio = (q->priority ? q->priority : 1.0);
	return (q->runcount + 1.0) / prio;
}

static inline enum wfq_state wfq_dequeue(struct wfq_queue *q)
{
	q->runcount++;
	return q->queue_fn(q);
}

static inline struct wfq_queue *wfq_process_next(struct wfq_queue *queues,
						 size_t cnt)
{
	struct wfq_queue *queue;
	enum wfq_state state;

	do {
		float vft = 0;
		unsigned int i = 0;

		queue = NULL;
		state = wfq_inactive;

		for (i = 0; i < cnt; ++i) {
			float this_vft;
			struct wfq_queue *q = &queues[i];

			if (!q->priority)
				continue;

			this_vft = wfq_get_finish_time(q);

			if (!vft || vft > this_vft) {
				vft   = this_vft;
				queue = q;
			}
		}
		if (queue)
			state = wfq_dequeue(queue);

	} while (queue && state == wfq_inactive);

	return queue;
}

struct fentry {
	struct stat stat;
	char *path;
};

struct fentry_list {
	struct fentry **list;
	size_t cap;
	size_t sz;
};

static inline void fentry_free(struct fentry *fe)
{
	if (!fe)
		return;
	free(fe->path);
	free(fe);
}

static inline struct fentry *fentry_alloc(const struct stat *stat,
					  const char *path)
{
	struct fentry *fe = malloc(sizeof(struct fentry));
	if (!fe)
		return NULL;

	fe->path = strdup(path);
	if (!fe->path)
		goto err;

	memcpy(&fe->stat, stat, sizeof(*stat));

	return fe;

err:
	fentry_free(fe);
	return NULL;
}

static inline int fentry_list_init(struct fentry_list *list, size_t cap)
{
	list->list = malloc(sizeof(struct fentry *) * cap);
	if (!list->list)
		return 0;
	list->cap = cap;
	list->sz = 0;
	return 1;
}

static inline void fentry_list_deinit(struct fentry_list *list)
{
	unsigned int i;

	for (i = 0; i < list->sz; ++i)
		fentry_free(list->list[i]);
	free(list->list);
}

static inline int fentry_list_push(struct fentry_list *list, struct fentry *fe)
{
	if (list->cap == list->sz) {
		size_t new_cap = list->cap << 1;
		struct fentry **new_list = realloc(list->list,
						   sizeof(struct fentry *) *
						   new_cap);
		if (!new_list)
			return 0;
		list->list = new_list;
		list->cap = new_cap;
	}

	list->list[list->sz++] = fe;
	return 1;
}

static int fentry_alphabetic_compare(const void *a_, const void *b_)
{
	const struct fentry * const *a = a_;
	const struct fentry * const *b = b_;
	return strcmp((*a)->path, (*b)->path);
}

static int fentry_random_compare(const void *a_, const void *b_)
{
	(void)a_;
	(void)b_;
	return rand() & 1;
}

static inline void fentry_list_sort(struct fentry_list *list,
				    int (*compar)(const void *, const void *))
{
	qsort(list->list, list->sz, sizeof(struct fentry *), compar);
}

static struct fentry_list *flist;

static int is_dot_dot_file(const char *p)
{
	return !strcmp(p, ".") || !strcmp(p, "..");
}

static int fentry_fill(const char *fpath, const struct stat *sb,
		       int tflag, struct FTW *ftwbuf)
{
	struct fentry *fe;
	(void)ftwbuf;

	if (tflag != FTW_F)
		return 0;
	if (!S_ISREG(sb->st_mode))
		return 0;
	if (is_dot_dot_file(fpath))
		return 0;

	fe = fentry_alloc(sb, fpath);
	if (!fe) {
		printf("memory allocation problems\n");
		return 0;
	}
	if (!fentry_list_push(flist, fe))
		printf("memory allocation problems\n");

	return 0;
}

static int fentry_list_fill(struct fentry_list *list, const char *path)
{
	fentry_list_init(list, 32);

	/* What we can do here? Just not to use threads */
	flist = list;

	if (nftw(path, fentry_fill, 32, FTW_PHYS) == -1) {
		perror("nftw");
		return 0;
	}

	return 1;
}

struct partition {
	unsigned long long start;
	unsigned long long end;
};

struct partition_list {
	struct partition *list;
	size_t cap;
	size_t sz;
	size_t ind;
};

static inline int partition_list_init(struct partition_list *list, size_t cap)
{
	list->list = malloc(sizeof(struct partition) * cap);
	if (!list->list)
		return 0;
	list->cap = cap;
	list->sz = 0;
	list->ind = 0;
	return 1;
}

static inline void partition_list_free(struct partition_list *list)
{
	if (!list)
		return;
	free(list->list);
	free(list);
}

static inline void partition_list_shuffle(struct partition_list *list,
					  unsigned int ratio)
{
	unsigned int i;
	unsigned int pos;

	if (!list || list->sz < 2)
		return;

	pos = ratio * list->sz / 100;

	for (i = list->sz - 1; pos < i; --i) {
		struct partition tmp;
		unsigned int j = rand_between(pos, i);
		if (i == j)
			continue;

		memcpy(&tmp, &list->list[i], sizeof(tmp));
		memcpy(&list->list[i], &list->list[j], sizeof(tmp));
		memcpy(&list->list[j], &tmp, sizeof(tmp));
	}
}

static inline unsigned int partition_count_crc32(struct partition *part,
						 FILE *file)
{
	int ret;
	unsigned int crc = 0;
	size_t buf_sz = (size_t)(part->end - part->start);
	void *buf;

	assert(part->end > part->start);
	buf = malloc(buf_sz);
	if (!buf) {
		printf("memory allocation problems\n");
		goto out;
	}
	ret = fseek(file, part->start, SEEK_SET);
	if (ret < 0) {
		perror("seek failed");
		goto out;
	}
	ret = do_fread(buf, buf_sz, file);
	if (ret < 0) {
		perror("read failed");
		goto out;
	}

	crc = crc32(buf, buf_sz, 0);

out:
	free(buf);

	return crc;
}

static inline struct partition *partition_list_next(struct partition_list *list)
{
	if (list->ind >= list->sz)
		return NULL;
	return &list->list[list->ind++];
}

static inline int partition_list_push(struct partition_list *list,
				      unsigned int start,
				      unsigned int end)
{
	struct partition part = {
		.start = start,
		.end = end
	};

	if (list->cap == list->sz) {
		size_t new_cap = list->cap << 1;
		struct partition *new_list = realloc(list->list,
						     sizeof(struct partition) *
						     new_cap);
		if (!new_list)
			return 0;
		list->list = new_list;
		list->cap = new_cap;
	}

	memcpy(&list->list[list->sz++], &part, sizeof(part));
	return 1;
}

static struct partition_list *do_random_partitioning(size_t min_block_size,
						     size_t max_block_size,
						     size_t whole_size)
{
	struct partition_list *part_list;
	unsigned int range, middle, middle_x2, blocks_x2_num;
	unsigned int i, off;

	if (min_block_size > max_block_size || !max_block_size) {
		assert(0);
		return NULL;
	}
	if (!whole_size)
		return NULL;

	part_list = malloc(sizeof(struct partition_list));
	if (!part_list)
		return NULL;
	if (!partition_list_init(part_list, 32)) {
		free(part_list);
		return NULL;
	}

	if (max_block_size > whole_size)
		max_block_size = whole_size;
	if (min_block_size > whole_size)
		min_block_size = whole_size;

	range = max_block_size - min_block_size;
	middle = min_block_size + range / 2;
	middle_x2 = middle * 2;

	blocks_x2_num = (whole_size + middle_x2 - 1) / middle_x2;

	for (i = 0, off = 0; i < blocks_x2_num; ++i, off += middle_x2) {
		unsigned int end, middle_point, rand_range;

		rand_range = rand_between(0, range) & ~511;

		middle_point = off + min_block_size + rand_range;
		end = off + middle_x2;

		middle_point = MIN(middle_point, whole_size);
		end = MIN(end, whole_size);

		if (!partition_list_push(part_list, off, middle_point)) {
			partition_list_free(part_list);
			return NULL;
		}
		if (end > middle_point) {
			if (!partition_list_push(part_list, middle_point,
						 end)) {
				partition_list_free(part_list);
				return NULL;
			}
		}
	}

	return part_list;
}

enum verif_state {
	verif_open_state = 0,
	verif_stat_state,
	verif_fetch_state,
	verif_close_state,
	verif_end_state
};

struct verif_common_args {
	unsigned int       *files_ind;
	struct fentry_list *files_list;
	struct bitset      *opened_bitset;
	struct wfq_queue   *map_read_queues;
	struct wfq_queue   *open_flags_queues;
	unsigned int       map_read_queues_sz;
	unsigned int       open_flags_queues_sz;
};

struct verif_args {
	struct verif_common_args *comm_arg;
	FILE                     *file;
	struct fentry            *fentry;
	struct partition_list    *parts;
	unsigned int             opened_ind;
	enum verif_state         state;
	char                     msg_buff[PATH_MAX + 256];
};

static enum wfq_state cache_queue_fn(struct wfq_queue *q)
{
	char **msg = (char **)&q->queue_arg;
	*msg = "O_CACHED";
	return wfq_active;
}

static enum wfq_state odirect_queue_fn(struct wfq_queue *q)
{
	char **msg = (char **)&q->queue_arg;
	*msg = "O_DIRECT";
	return wfq_active;
}

static enum wfq_state read_queue_fn(struct wfq_queue *q)
{
	char **msg = (char **)&q->queue_arg;
	*msg = "read";
	return wfq_active;
}

static enum wfq_state mmap_queue_fn(struct wfq_queue *q)
{
	char **msg = (char **)&q->queue_arg;
	*msg = "mmap";
	return wfq_active;
}

static enum wfq_state verif_open_fn(struct wfq_queue *q)
{
	struct verif_args *arg = q->queue_arg;
	struct verif_common_args *comm_arg = arg->comm_arg;
	struct fentry_list *flist = comm_arg->files_list;
	struct wfq_queue *open_q;
	struct fentry *fe;

	/* Stop the queue if there is no file to read */
	if (*comm_arg->files_ind >= flist->sz) {
		arg->state = verif_end_state;
		q->priority = 0;
		return wfq_inactive;
	}

	/* Should be closed */
	assert(!arg->file);
	assert(!arg->fentry);

	fe = flist->list[(*comm_arg->files_ind)++];
	arg->file = fopen(fe->path, "r");
	if (!arg->file) {
		printf("can't open file '%s', errno %u\n", fe->path, errno);
		return wfq_inactive;
	}

	open_q = wfq_process_next(arg->comm_arg->open_flags_queues,
				  arg->comm_arg->open_flags_queues_sz);
	assert(open_q);

	arg->opened_ind = bitset_fcb(arg->comm_arg->opened_bitset);
	bitset_set(arg->comm_arg->opened_bitset, arg->opened_ind);
	arg->state = verif_stat_state;
	arg->fentry = fe;
	arg->parts = do_random_partitioning(arg_min_block_size,
					    arg_max_block_size,
					    fe->stat.st_size);
	/* Shuffle partitions */
	if (arg->parts && arg_io_seq != 100)
		partition_list_shuffle(arg->parts, arg_io_seq);

	snprintf(arg->msg_buff, sizeof(arg->msg_buff),
		 "open(\"%s\", %s) = %d\n",
		 arg->fentry->path, (const char *)open_q->queue_arg,
		 arg->opened_ind);

	return wfq_active;
}

static enum wfq_state verif_stat_fn(struct wfq_queue *q)
{
	struct verif_args *arg = q->queue_arg;
	arg->state = verif_fetch_state;
	snprintf(arg->msg_buff, sizeof(arg->msg_buff),
		 "stat(\"%s\", %d) = (%u, %u, %llu)\n",
		 arg->fentry->path, arg->opened_ind,
		 (unsigned int)arg->fentry->stat.st_uid,
		 (unsigned int)arg->fentry->stat.st_gid,
		 (unsigned long long)arg->fentry->stat.st_size);
	return wfq_active;
}

static enum wfq_state verif_fetch_fn(struct wfq_queue *q)
{
	struct verif_args *arg = q->queue_arg;
	struct partition *part;
	unsigned int crc32;
	struct wfq_queue *fetch_q;

	/* Get next partition block if partition list was created */
	part = arg->parts ? partition_list_next(arg->parts) : NULL;

	/* Partitioning failed on previous state because
	 * of possible zero file size. Or next block is undef,
	 * because we reach EOF. Do close in any case */
	if (!part) {
		arg->state = verif_close_state;
		return wfq_repeat;
	}

	fetch_q = wfq_process_next(arg->comm_arg->map_read_queues,
				   arg->comm_arg->map_read_queues_sz);
	assert(fetch_q);

	crc32 = partition_count_crc32(part, arg->file);
	if (!crc32)
		return wfq_inactive;

	snprintf(arg->msg_buff, sizeof(arg->msg_buff),
		 "%s(\"%s\", %d, %llu, %llu) = crc32(0x%08x)\n",
		 (const char *)fetch_q->queue_arg, arg->fentry->path,
		 arg->opened_ind, part->start, part->end,
		 crc32);

	return wfq_active;
}

static enum wfq_state verif_close_fn(struct wfq_queue *q)
{
	struct verif_args *arg = q->queue_arg;

	bitset_clear(arg->comm_arg->opened_bitset, arg->opened_ind);
	arg->state = verif_open_state;

	snprintf(arg->msg_buff, sizeof(arg->msg_buff),
		 "close(\"%s\", %d)\n", arg->fentry->path, arg->opened_ind);
	if (fclose(arg->file))
		perror("close failed");
	partition_list_free(arg->parts);
	arg->parts = NULL;
	arg->file = NULL;
	arg->fentry = NULL;
	return wfq_active;
}

static enum wfq_state verif_end_fn(struct wfq_queue *q)
{
	(void)q;
	abort();
	return wfq_inactive;
}

typedef enum wfq_state (*verif_fn)(struct wfq_queue *);
static verif_fn state_verif_table[] = {
	verif_open_fn,
	verif_stat_fn,
	verif_fetch_fn,
	verif_close_fn,
	verif_end_fn
};

static enum wfq_state verif_queue_fn(struct wfq_queue *q)
{
	enum wfq_state queue_state;
	struct verif_args *arg = q->queue_arg;

	do {
		queue_state = state_verif_table[arg->state](q);
	} while (queue_state == wfq_repeat);

	return queue_state;
}

static int gen_verif_list(struct fentry_list *flist, FILE *fout)
{
	int ret;
	unsigned int i;
	unsigned int files_ind = 0;
	unsigned int lines_cnt = 0;
	unsigned int verif_queues_num = arg_opened;
	struct bitset *opened_bitset = NULL;
	struct verif_common_args comm_arg;
	struct verif_args *verif_args = NULL;
	struct wfq_queue  *verif_queues = NULL;
	struct wfq_queue  *q = NULL;

	struct wfq_queue open_flags_queues[] = {{
			.priority = 100 - arg_odirect,
			.runcount = 0,
			.queue_fn = cache_queue_fn,
			.queue_arg = NULL
		}, {
			.priority = arg_odirect,
			.runcount = 0,
			.queue_fn = odirect_queue_fn,
			.queue_arg = NULL
		}
	};
	struct wfq_queue map_read_queues[] = {{
			.priority = 100 - arg_mmap,
			.runcount = 0,
			.queue_fn = read_queue_fn,
			.queue_arg = NULL
		}, {
			.priority = arg_mmap,
			.runcount = 0,
			.queue_fn = mmap_queue_fn,
			.queue_arg = NULL
		}
	};

	assert(verif_queues_num);
	opened_bitset = bitset_alloc(verif_queues_num);
	if (!opened_bitset) {
		ret = 0;
		goto out;
	}

	verif_queues = calloc(sizeof(*verif_queues), verif_queues_num);
	if (!verif_queues) {
		ret = 0;
		goto out;
	}

	verif_args = calloc(sizeof(*verif_args), verif_queues_num);
	if (!verif_args) {
		ret = 0;
		goto out;
	}

	/* Init common args for every queue */
	comm_arg = (struct verif_common_args) {
		.files_ind            = &files_ind,
		.files_list           = flist,
		.opened_bitset        = opened_bitset,
		.map_read_queues      = map_read_queues,
		.open_flags_queues    = open_flags_queues,
		.map_read_queues_sz   = ARRAY_SIZE(map_read_queues),
		.open_flags_queues_sz = ARRAY_SIZE(open_flags_queues),
	};

	/* Init main verification queues */
	for (i = 0; i < verif_queues_num; ++i) {
		struct wfq_queue  *q = &verif_queues[i];
		struct verif_args *arg = &verif_args[i];
		q->priority  = 1;
		q->runcount  = 0;
		q->queue_fn  = verif_queue_fn;
		q->queue_arg = arg;

		arg->comm_arg   = &comm_arg;
		arg->file       = NULL;
		arg->fentry     = NULL;
		arg->parts      = NULL;
		arg->opened_ind = 0;
		arg->state      = verif_open_state;
	}

	/* Loop till end */
	while ((q = wfq_process_next(verif_queues, verif_queues_num))) {
		struct verif_args *arg = q->queue_arg;
		progress("scanning", files_ind, flist->sz);
		ret = fprintf(fout, "%s", arg->msg_buff);
		if (ret < 0) {
			perror("failed writing to file");
			ret = 0;
			goto out;
		}
		lines_cnt++;
	}

	/* Some sanity checks */
	if (0 != bitset_fcb(opened_bitset))
		assert(0);
	if (files_ind != flist->sz)
		assert(0);

	ret = 1;

out:
	bitset_free(opened_bitset);
	free(verif_queues);
	free(verif_args);

	return ret;
}

static void fatal(const char *x, ...)
{
	va_list ap;

	va_start(ap, x);
	vfprintf(stderr, x, ap);
	va_end(ap);
	exit(EXIT_FAILURE);
}

static int do_generate(FILE *file)
{
	struct fentry_list flist;

	if (arg_seed)
		srand(*arg_seed);

	if (!fentry_list_fill(&flist, arg_dir_name))
		return 1;

	if (arg_shuffle)
		fentry_list_sort(&flist, fentry_random_compare);
	else
		fentry_list_sort(&flist, fentry_alphabetic_compare);

	if (!gen_verif_list(&flist, file))
		return 1;

	return 0;
}

static const char *prepare_path(const char *path, const char *dir,
				int skip_prefix,
				char *buff, size_t size)
{
	while (path && skip_prefix--) {
		path = strchr(path, '/');
		if (path)
			path += 1;
	}
	if (path && dir) {
		assert(buff && size);
		snprintf(buff, size, "%s/%s", dir, path);
		path = buff;
	}
	return path;
}

static ssize_t do_pread(int fildes, void *buf, size_t nbyte, off_t offset)
{
	ssize_t ret = 0, r;
	do {
		r = pread(fildes, buf + ret, nbyte - ret, offset + ret);
		if (r > 0)
			ret += r;
	} while (r > 0 && (size_t)ret != nbyte);

	return ret;
}

static void execute_OPEN(const char *line, size_t len, int *handles,
			 size_t handles_sz)
{
	char path_buf[256];
	char buf[256];
	const char *path;
	char flags[16];
	unsigned int f_desc;
	int ret;
	int open_flags;
	unsigned int *stat;

	(void)len;

	ret = sscanf(line, "open(\"%256[^\"]\", %16[^)]) = %u",
		     path_buf, flags, &f_desc);
	if (ret != 3) {
		printf("WARNING: OPEN cmd is malformed: '%s'\n", line);
		return;
	}

	if (0 == strncmp("O_CACHED", flags, sizeof(flags))) {
		open_flags = O_LARGEFILE | O_RDONLY;
		stat = &global_stat.cached;
	} else if (0 == strncmp("O_DIRECT", flags, sizeof(flags))) {
		open_flags = O_LARGEFILE | O_RDONLY | O_DIRECT;
		stat = &global_stat.odirects;
	} else {
		printf("WARNING: OPEN cmd is malformed, unknown "
		       "flags: '%s'\n", line);
		return;
	}

	if (f_desc >= handles_sz) {
		printf("WARNING: OPEN cmd is malformed, descriptor "
		       "exceeds %u: '%s'\n",
		       (unsigned)handles_sz, line);
		return;
	}

	if (-1 != handles[f_desc]) {
		printf("WARNING: OPEN cmd is malformed, descriptor "
		       "is already occupied '%s'\n", line);
		return;
	}
	path = prepare_path(path_buf, arg_dir_name, arg_skip_prefix,
			    buf, sizeof(buf));
	if (!path) {
		printf("WARNING: path became NULL, wrong prefix?, '%s', "
		       "err %u\n", line, errno);
		return;
	}

	handles[f_desc] = open(path, open_flags);
	if (-1 == handles[f_desc]) {
		printf("WARNING: can't open file for reading, '%s', "
		       "err %u\n", line, errno);
		return;
	}

	++*stat;
}

static void execute_STAT(const char *line, size_t len, int *handles,
			 size_t handles_sz)
{
	char path[256];
	unsigned int f_desc;
	int ret;
	unsigned int uid, gid;
	long long int size;
	struct stat stat;

	(void)len;

	ret = sscanf(line, "stat(\"%256[^\"]\", %u) = (%u, %u, %lld)",
		     path, &f_desc, &uid, &gid, &size);
	if (ret != 5) {
		printf("WARNING: STAT cmd is malformed: '%s'\n", line);
		return;
	}

	if (f_desc >= handles_sz) {
		printf("WARNING: STAT cmd is malformed, descriptor "
		       "exceeds %u: '%s'\n",
		       (unsigned)handles_sz, line);
		return;
	}

	if (-1 == handles[f_desc]) {
		printf("WARNING: STAT cmd is malformed, invalid "
		       "handle: '%s'\n", line);
		return;
	}

	ret = fstat(handles[f_desc], &stat);
	if (ret) {
		printf("WARNING: can't stat file, '%s', err %u\n",
		       line, errno);
		return;
	}

	if (stat.st_size != size ||
	    stat.st_uid != uid ||
	    stat.st_gid != gid) {
		printf("WARNING: stat info differs, '%s', "
		       "stat (size %lld, uid %u, gid %u), "
		       "real stat (size %lld, uid %u, gid %u)\n",
		       line, size, uid, gid,
		       (long long int)stat.st_size,
		       stat.st_uid, stat.st_gid);

		global_stat.err_stats++;
		return;
	}
}

static void execute_READ(const char *line, size_t len, int *handles,
			 size_t handles_sz)
{
	const unsigned int max_buf_size = 1<<20;
	unsigned int block_size, buf_size;
	void *buff;
	char path[256];
	unsigned int f_desc;
	unsigned long long start_pos, end_pos;
	unsigned long long msecs;
	int crc, real_crc;
	int ret;

	(void)len;

	ret = sscanf(line, "read(\"%256[^\"]\", %u, %llu, %llu) = "
		     "crc32(0x%x)", path, &f_desc, &start_pos,
		     &end_pos, &crc);
	if (ret != 5) {
		printf("WARNING: READ cmd is malformed: '%s'\n", line);
		return;
	}

	if (f_desc >= handles_sz) {
		printf("WARNING: READ cmd is malformed, descriptor "
		       "exceeds %u: '%s'\n",
		       (unsigned)handles_sz, line);
		return;
	}

	if (-1 == handles[f_desc]) {
		printf("WARNING: READ cmd is malformed, invalid "
		       "handle: '%s'\n", line);
		return;
	}

	block_size = (unsigned int)(end_pos - start_pos);
	buf_size = round_up(block_size, 512);
	if (buf_size > max_buf_size) {
		printf("WARNING: READ cmd is malformed, buf size "
		       "exceeded max size '%u': '%s'\n",
		       max_buf_size, line);
		return;
	}

	buff = memalign(4096, buf_size);
	if (!buff) {
		printf("WARNING: can't allocate memory for buffer: '%s'\n",
		       line);
		return;
	}

	msecs = msecs_epoch();

	ret = do_pread(handles[f_desc], buff, buf_size, start_pos);
	if (ret != (ssize_t)block_size) {
		printf("WARNING: read from file failed, '%s', ret %u, "
		       "err %u\n", line, ret, errno);
		goto out;
	}

	real_crc = crc32(buff, block_size, 0);
	if (real_crc != crc) {
		printf("WARNING: crc32 failed, '%s', crc32 0x%08x\n",
		       line, real_crc);
		global_stat.err_reads++;
		goto out;
	}

	/* yes, crc calculation is also included */
	global_stat.msecs += msecs_epoch() - msecs;
	global_stat.bytes += block_size;
	global_stat.reads++;

out:
	free(buff);
}

static void execute_MMAP(const char *line, size_t len, int *handles,
			 size_t handles_sz)
{
	const unsigned int max_buf_size = 1<<20;
	unsigned int block_size, buf_size;
	void *buff;
	char path[256];
	unsigned int f_desc;
	unsigned long long start_pos, end_pos;
	unsigned long long msecs;
	unsigned long long start_pos_aligned, end_pos_aligned;
	int crc, real_crc;
	int ret;

	(void)len;

	ret = sscanf(line, "mmap(\"%256[^\"]\", %u, %llu, %llu) = "
		     "crc32(0x%x)", path, &f_desc, &start_pos,
		     &end_pos, &crc);
	if (ret != 5) {
		printf("WARNING: MMAP cmd is malformed: '%s'\n", line);
		return;
	}

	if (f_desc >= handles_sz) {
		printf("WARNING: MMAP cmd is malformed, descriptor "
		       "exceeds %u: '%s'\n",
		       (unsigned)handles_sz, line);
		return;
	}

	if (-1 == handles[f_desc]) {
		printf("WARNING: MMAP cmd is malformed, invalid "
		       "handle: '%s'\n", line);
		return;
	}

	block_size = (unsigned int)(end_pos - start_pos);
	start_pos_aligned = round_down(start_pos, 4096ull);
	end_pos_aligned = round_up(end_pos, 4096ull);
	buf_size = end_pos_aligned - start_pos_aligned;

	if (buf_size > max_buf_size) {
		printf("WARNING: MMAP cmd is malformed, buf size "
		       "exceeded max size '%u': '%s'\n",
		       max_buf_size, line);
		return;
	}

	msecs = msecs_epoch();

	buff = mmap(NULL, buf_size, PROT_READ, MAP_PRIVATE,
		    handles[f_desc], start_pos_aligned);
	if (buff == MAP_FAILED) {
		printf("WARNING: mmap failed, '%s', err %u\n",
		       line, errno);
		return;
	}

	real_crc = crc32(buff + (start_pos & 4095), block_size, 0);
	if (real_crc != crc) {
		printf("WARNING: crc32 failed, '%s', crc32 0x%08x\n",
		       line, real_crc);
		global_stat.err_mmaps++;
		goto out;
	}

	/* yes, crc calculation is also included */
	global_stat.msecs += msecs_epoch() - msecs;
	global_stat.bytes += block_size;
	global_stat.mmaps++;

out:
	munmap(buff, buf_size);
}

static void execute_CLOSE(const char *line, size_t len, int *handles,
			  size_t handles_sz)
{
	char path[256];
	unsigned int f_desc;
	int ret;

	(void)len;

	ret = sscanf(line, "close(\"%256[^\"]\", %u)", path, &f_desc);
	if (ret != 2) {
		printf("WARNING: CLOSE cmd is malformed: '%s'\n", line);
		return;
	}

	if (f_desc >= handles_sz) {
		printf("WARNING: CLOSE cmd is malformed, descriptor "
		       "exceeds %u: '%s'\n",
		       (unsigned)handles_sz, line);
		return;
	}

	if (-1 == handles[f_desc]) {
		printf("WARNING: CLOSE cmd is malformed, descriptor "
		       "was never opened '%s'\n", line);
		return;
	}

	ret = close(handles[f_desc]);
	handles[f_desc] = -1;
	if (ret) {
		printf("WARNING: can't close file, '%s', err %u\n",
		       line, errno);
		return;
	}
}

static void execute_cmd(const char *line, size_t len, int *handles,
			size_t handles_sz)
{
	if (0 == strncmp(OPEN_CMD, line,
			 MIN(len, strlen(OPEN_CMD)))) {
		execute_OPEN(line, len, handles, handles_sz);
	} else if (0 == strncmp(STAT_CMD, line,
				MIN(len, strlen(STAT_CMD)))) {
		execute_STAT(line, len, handles, handles_sz);
	} else if (0 == strncmp(READ_CMD, line,
				MIN(len, strlen(READ_CMD)))) {
		execute_READ(line, len, handles, handles_sz);
	} else if (0 == strncmp(MMAP_CMD, line,
				MIN(len, strlen(MMAP_CMD)))) {
		execute_MMAP(line, len, handles, handles_sz);
	} else if (0 == strncmp(CLOSE_CMD, line,
				MIN(len, strlen(CLOSE_CMD)))) {
		execute_CLOSE(line, len, handles, handles_sz);
	} else
		printf("WARNING: unrecognized cmd '%s'\n", line);
}

static void verif_execute_list(FILE *list_h, int *handles, size_t handles_sz)
{
	char *line = NULL;
	size_t len = 0;
	ssize_t read;
	struct stat stat;
	unsigned long long total = 0;

	/* Get file size to calculate progress */
	if (fstat(fileno(list_h), &stat) < 0) {
		perror("failed getting stat of input file");
		goto out;
	}

	/* Read contents */
	while ((read = getline(&line, &len, list_h)) != -1) {
		progress("verifying", total, stat.st_size);
		execute_cmd(line, len, handles, handles_sz);
		total += read;
	}

out:
	free(line);
}

static int do_verify(FILE *file)
{
	int handles[MAX_OPENED];
	unsigned long long tm;
	float secs;

	memset(handles, -1, sizeof(handles));
	crc32_init();

	tm = msecs_epoch();

	/* Execute everything from list */
	verif_execute_list(file, handles, MAX_OPENED);

	secs = (msecs_epoch() - tm) / 1000.0;

	/* Print out stats info */
	printf("Verification\n"
	       "  time:                         %8.3f s\n"
	       "  bandwidth:                    %8llu kb/s\n"
	       "\n"
	       "Verified files:                 %8u\n"
	       "  opened as cached:             %8u\n"
	       "  opened as O_DIRECT:           %8u\n"
	       "\n"
	       "Checked blocks:                 %8u\n"
	       "  using read:                   %8u\n"
	       "  using mmap:                   %8u\n"
	       "\n"
	       "Errors:                         %8u\n"
	       "  stats mismatch:               %8u\n"
	       "  reads CRC mismatch:           %8u\n"
	       "  mmaps CRC mismatch:           %8u\n",
	       secs,
	       global_stat.bytes / global_stat.msecs,
	       global_stat.cached +
	       global_stat.odirects,
	       global_stat.cached,
	       global_stat.odirects,

	       global_stat.reads +
	       global_stat.mmaps,
	       global_stat.reads,
	       global_stat.mmaps,

	       global_stat.err_stats +
	       global_stat.err_reads +
	       global_stat.err_mmaps,
	       global_stat.err_stats,
	       global_stat.err_reads,
	       global_stat.err_mmaps);

	return 0;
}

static int parse_io_seq(const char *opts,
			unsigned int *io_seq)
{
	if (1 == sscanf(opts, "seq=%u", io_seq))
		return *io_seq <= 100;
	else if (1 == sscanf(opts, "random=%u", io_seq)) {
		if (*io_seq > 100)
			return 0;
		*io_seq = 100 - *io_seq;
		return 1;
	}
	return 0;
}

static int parse_block_size(const char *opts,
			    unsigned int *min_block_size,
			    unsigned int *max_block_size)
{
	if (2 == sscanf(opts, "%u-%u", min_block_size, max_block_size))
		goto check;
	else if (1 == sscanf(opts, "%u", min_block_size)) {
		*max_block_size = *min_block_size;
		goto check;
	}
	return 0;

check:
	if (*min_block_size > *max_block_size ||
	    *min_block_size == 0 || *max_block_size > (1<<20))
		return 0;

	*min_block_size *= 512;
	*max_block_size *= 512;

	return 1;
}

static int parse_verify_opts(const char *opts,
			     unsigned int *odirect,
			     unsigned int *mmap)
{
	if (1 == sscanf(opts, "mmap=%u", mmap))
		return *mmap <= 100;
	else if (1 == sscanf(opts, "odirect=%u", odirect))
		return *odirect <= 100;
	return 0;
}

static int parse_opened(const char *opts,
			unsigned int *opened)
{
	*opened = atoi(opts);
	return (*opened >= 1 && *opened <= 256);
}

static int parse_order(const char *opts,
		       unsigned int *order)
{
	if (0 == strcmp(opts, "order"))
		*order = 0;
	else if (0 == strcmp(opts, "shuffle"))
		*order = 1;
	else
		return 0;
	return 1;
}

static void usage(void)
{
	printf("Simple tool for files verification.\n\n"
	       "fverify generate [-dfosOibV] Generate verification list\n"
	       "\t-q|--quiet            Quiet mode, do not output progress\n"
	       "\t-f|--file   <file>    Output file for verification "
	       "list\n"
	       "\t-d|--dir    <dir>     Directory against verification "
	       "list should be generated\n"

	       "\t-o|--order  <option>  Order of files in list\n"
	       "\t\tsort    - alphabetic sort\n"
	       "\t\tshuffle - random shuffle\n"
	       "\t-s|--seed   <value>   Seed value for random generator\n"
	       "\t-O|--opened <value>   Simultaneously opened files\n"
	       "\t-i|--io     <option>  IO type to be done\n"
	       "\t\tseq=ratio    - do sequential IO, in the ratio seq to "
	       "random\n"
	       "\t\trandom=ratio - do random IO, in the ratio random to "
	       "seq\n"
	       "\t-b|--block <sec|sec-sec> Block size in sectors. Also "
	       "you can specify range, in that case random block size "
	       "will be generated\n"
	       "\t-V|--verify <option>  Verification options\n"
	       "\t\tmmap=ratio    - use mmap, in the ratio of mmaps to "
	       "plain reads\n"
	       "\t\todirect=ratio - open files with odirect, in the ratio "
	       "opens with O_DIRECT to original cached opens\n"
	       "\n"
	       "fverify verify [-fdp]  Verify list\n"
	       "\t-q|--quiet            Quiet mode, do not output progress\n"
	       "\t-f|--file   <file>    Input verification list\n"
	       "\t-d|--dir    <dir>     Directory against verification "
	       "should be done\n"
	       "\t-p|--prefix <number>  Strip prefix from each file name "
	       "(similar to patch -pX)\n"
	       "\n"
	       "common options\n"
	       "\t-h|--help             Show usage information\n"
		);
}

struct option verify_opts[] = {
	{ "file",   required_argument, NULL, 'f' },
	{ "dir" ,   required_argument, NULL, 'd' },
	{ "prefix", required_argument, NULL, 'p' },
	{ "quiet",  no_argument,       NULL, 'q' },
	{ "help",   no_argument,       NULL, 'h' },
	{ NULL, 0, NULL, 0 }
};
const char *verify_opts_str = "f:d:p:qh";

struct option generate_opts[] = {
	{ "file",   required_argument, NULL, 'f'  },
	{ "dir" ,   required_argument, NULL, 'd'  },
	{ "order",  required_argument, NULL, 'o' },
	{ "seed",   required_argument, NULL, 's' },
	{ "opened", required_argument, NULL, 'O' },
	{ "io",     required_argument, NULL, 'i' },
	{ "block",  required_argument, NULL, 'b' },
	{ "verify", required_argument, NULL, 'V' },
	{ "quiet",  no_argument,       NULL, 'q'  },
	{ "help",   no_argument,       NULL, 'h'  },
	{ NULL, 0, NULL, 0 }
};
const char *generate_opts_str = "f:d:o:s:O:i:b:V:qh";

int main(int argc, char *argv[])
{
	int c, ret;
	int generate_mode = 0;
	FILE *file;
	struct option *opts = verify_opts;
	const char *opts_str = verify_opts_str;
	int seed;

	if (argc < 2) {
		usage();
		return 1;
	}

	/* Check that generate or verify is specified */
	if (0 == strcmp(argv[1], "generate")) {
		generate_mode = 1;
		opts = generate_opts;
		opts_str = generate_opts_str;
	} else if (0 != strcmp(argv[1], "verify")) {
		usage();
		return 1;
	}

	while ((c = getopt_long(argc - 1, argv + 1, opts_str,
				opts, NULL)) != -1) {
		switch (c) {
			/* Common opts */
		case 'h':
			usage();
			return 0;
		case 'q':
			arg_quiet = 1;
			break;
		case 'f':
			arg_file_name = optarg;
			break;
		case 'd':
			arg_dir_name = optarg;
			break;
			/* Verify opts */
		case 'p':
			arg_skip_prefix = atoi(optarg);
			break;
			/* Generate opts */
		case 'o':
			if (!parse_order(optarg, &arg_shuffle)) {
				usage();
				return 1;
			}
			break;
		case 's':
			seed = atoi(optarg);
			arg_seed = &seed;
			break;
		case 'O':
			if (!parse_opened(optarg, &arg_opened)) {
				usage();
				return 1;
			}
			break;
		case 'i':
			if (!parse_io_seq(optarg, &arg_io_seq)) {
				usage();
				return 1;
			}
			break;
		case 'b':
			if (!parse_block_size(optarg, &arg_min_block_size,
					      &arg_max_block_size)) {
				usage();
				return 1;
			}
			break;
		case 'V':
			if (!parse_verify_opts(optarg, &arg_odirect,
					       &arg_mmap)) {
				usage();
				return 1;
			}
			break;
		default:
			return 1;
		}
	}

	/* Obligatory params */
	if (generate_mode) {
		if (!arg_dir_name || !arg_min_block_size) {
			usage();
			return 1;
		}
	}

	file = fopen(arg_file_name, generate_mode ? "w" : "r");
	if (file == NULL)
		fatal("can't open source file %s\n", arg_file_name);
	if (generate_mode)
		ret = do_generate(file);
	else
		ret = do_verify(file);

	fclose(file);

	return ret;
}
