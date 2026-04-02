/* SPDX-License-Identifier: BSD-3-Clause
 * TLA+ trace harness for DPDK rte_ring.
 *
 * Standalone program: creates rings and exercises enqueue/dequeue
 * to produce NDJSON traces for TLA+ trace validation.
 *
 * Build: see harness/run.sh
 * Usage: TRACE_DIR=../traces ./test_ring_trace --no-huge --lcores=0,1,2
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <rte_eal.h>
#include <rte_errno.h>
#include <rte_ring.h>
#include <rte_lcore.h>
#include <rte_launch.h>
#include <rte_pause.h>
#include <rte_atomic.h>
#include "rte_ring_tla_trace.h"

/* ================================================================
 * Helpers
 * ================================================================ */

static const char *trace_dir = "../traces";

static void
open_trace(const char *name)
{
	char path[256];
	snprintf(path, sizeof(path), "%s/%s.ndjson", trace_dir, name);
	tla_trace_open(path);
}

/* Barrier for synchronizing multi-lcore tests */
static volatile RTE_ATOMIC(int) barrier_cnt;
static volatile RTE_ATOMIC(int) go_flag;

static void
sync_barrier(int total)
{
	if (rte_atomic_fetch_add_explicit(&barrier_cnt, 1,
			rte_memory_order_acq_rel) == total - 1) {
		/* Last thread to arrive: release all */
		rte_atomic_store_explicit(&go_flag, 1,
				rte_memory_order_release);
	} else {
		while (!rte_atomic_load_explicit(&go_flag,
				rte_memory_order_acquire))
			rte_pause();
	}
}

static void
reset_barrier(void)
{
	rte_atomic_store_explicit(&barrier_cnt, 0,
			rte_memory_order_relaxed);
	rte_atomic_store_explicit(&go_flag, 0,
			rte_memory_order_relaxed);
}

/* ================================================================
 * Scenario 1: basic_mpmc
 *
 * Single-threaded MPMC: main lcore enqueues 3 items then dequeues 3.
 * Exercises the full Reserve→Write→PublishTail sequence.
 *
 * Trace.cfg: Thread={t1,t2,t3}, Capacity=3, Mode="MPMC", MaxBatch=1
 * Only t1 is active; t2, t3 stay Idle.
 * ================================================================ */

static int
test_basic_mpmc(void)
{
	printf("=== basic_mpmc ===\n");

	struct rte_ring *r = rte_ring_create("basic_mpmc", 3,
			SOCKET_ID_ANY, RING_F_EXACT_SZ);
	if (!r) {
		fprintf(stderr, "Failed to create ring\n");
		return -1;
	}

	open_trace("basic_mpmc");
	tla_trace_set_thread_id(1);

	void *obj;
	int ret;

	/* Enqueue 3 items */
	obj = (void *)(uintptr_t)100;
	ret = rte_ring_mp_enqueue(r, obj);
	printf("  enqueue 1: %s\n", ret == 0 ? "ok" : "fail");

	obj = (void *)(uintptr_t)200;
	ret = rte_ring_mp_enqueue(r, obj);
	printf("  enqueue 2: %s\n", ret == 0 ? "ok" : "fail");

	obj = (void *)(uintptr_t)300;
	ret = rte_ring_mp_enqueue(r, obj);
	printf("  enqueue 3: %s (ring should be full)\n",
		ret == 0 ? "ok" : "fail");

	/* Dequeue 3 items */
	ret = rte_ring_mc_dequeue(r, &obj);
	printf("  dequeue 1: %s (val=%lu)\n",
		ret == 0 ? "ok" : "fail", (uintptr_t)obj);

	ret = rte_ring_mc_dequeue(r, &obj);
	printf("  dequeue 2: %s (val=%lu)\n",
		ret == 0 ? "ok" : "fail", (uintptr_t)obj);

	ret = rte_ring_mc_dequeue(r, &obj);
	printf("  dequeue 3: %s (val=%lu)\n",
		ret == 0 ? "ok" : "fail", (uintptr_t)obj);

	tla_trace_close();
	rte_ring_free(r);

	printf("  basic_mpmc done\n");
	return 0;
}

/* ================================================================
 * Scenario 2: concurrent_mpmc
 *
 * 3 lcores: t1 and t2 each enqueue 1 item, t3 dequeues 2 items.
 * Real concurrency — producers run simultaneously, consumer waits.
 *
 * Trace.cfg: Thread={t1,t2,t3}, Capacity=3, Mode="MPMC", MaxBatch=1
 * ================================================================ */

static struct rte_ring *concurrent_ring;
static volatile RTE_ATOMIC(int) producers_done;

/* Producer worker: enqueue one item */
static int
concurrent_producer(void *arg)
{
	int tid = (int)(uintptr_t)arg;
	tla_trace_set_thread_id(tid);

	/* Wait for all threads to be ready */
	sync_barrier(3);

	void *obj = (void *)(uintptr_t)(tid * 100);
	rte_ring_mp_enqueue(concurrent_ring, obj);

	/* Signal done */
	rte_atomic_fetch_add_explicit(&producers_done, 1,
			rte_memory_order_release);
	return 0;
}

/* Consumer worker: dequeue items after producers finish */
static int
concurrent_consumer(void *arg)
{
	int tid = (int)(uintptr_t)arg;
	tla_trace_set_thread_id(tid);

	/* Wait for all threads to be ready */
	sync_barrier(3);

	/* Wait for both producers to finish */
	while (rte_atomic_load_explicit(&producers_done,
			rte_memory_order_acquire) < 2)
		rte_pause();

	/* Small delay to ensure PublishTail completes */
	usleep(1000);

	void *obj;
	rte_ring_mc_dequeue(concurrent_ring, &obj);
	rte_ring_mc_dequeue(concurrent_ring, &obj);

	return 0;
}

static int
test_concurrent_mpmc(void)
{
	unsigned int lc;
	unsigned int workers[3];
	int nworkers = 0;

	/* Collect available worker lcores */
	RTE_LCORE_FOREACH_WORKER(lc) {
		if (nworkers < 2) {
			workers[nworkers] = lc;
			nworkers++;
		}
	}

	if (nworkers < 2) {
		printf("=== concurrent_mpmc: SKIPPED (need 2 worker lcores, "
		       "use --lcores=0,1,2) ===\n");
		return 0;
	}

	printf("=== concurrent_mpmc ===\n");

	concurrent_ring = rte_ring_create("conc_mpmc", 3,
			SOCKET_ID_ANY, RING_F_EXACT_SZ);
	if (!concurrent_ring) {
		fprintf(stderr, "Failed to create ring\n");
		return -1;
	}

	open_trace("concurrent_mpmc");
	rte_atomic_store_explicit(&producers_done, 0,
			rte_memory_order_relaxed);
	reset_barrier();

	/* Launch: worker 0 = producer t1, worker 1 = producer t2 */
	rte_eal_remote_launch(concurrent_producer,
			(void *)(uintptr_t)1, workers[0]);
	rte_eal_remote_launch(concurrent_consumer,
			(void *)(uintptr_t)3, workers[1]);

	/* Main lcore = producer t2 */
	tla_trace_set_thread_id(2);
	sync_barrier(3);

	void *obj = (void *)(uintptr_t)200;
	rte_ring_mp_enqueue(concurrent_ring, obj);
	rte_atomic_fetch_add_explicit(&producers_done, 1,
			rte_memory_order_release);

	/* Wait for workers */
	RTE_LCORE_FOREACH_WORKER(lc)
		rte_eal_wait_lcore(lc);

	tla_trace_close();
	rte_ring_free(concurrent_ring);

	printf("  concurrent_mpmc done\n");
	return 0;
}

/* ================================================================
 * Scenario 3: basic_hts
 *
 * Single-threaded HTS mode: enqueue 2, dequeue 2.
 * HTS serializes access (head==tail gate), so single-thread is the
 * natural mode.
 *
 * Needs separate Trace.cfg with Mode="HTS".
 * ================================================================ */

static int
test_basic_hts(void)
{
	printf("=== basic_hts ===\n");

	struct rte_ring *r = rte_ring_create("basic_hts", 3,
			SOCKET_ID_ANY,
			RING_F_EXACT_SZ | RING_F_MP_HTS_ENQ |
			RING_F_MC_HTS_DEQ);
	if (!r) {
		fprintf(stderr, "Failed to create HTS ring\n");
		return -1;
	}

	open_trace("basic_hts");
	tla_trace_set_thread_id(1);

	void *obj;
	int ret;

	obj = (void *)(uintptr_t)10;
	ret = rte_ring_enqueue(r, obj);
	printf("  hts enqueue 1: %s\n", ret == 0 ? "ok" : "fail");

	obj = (void *)(uintptr_t)20;
	ret = rte_ring_enqueue(r, obj);
	printf("  hts enqueue 2: %s\n", ret == 0 ? "ok" : "fail");

	ret = rte_ring_dequeue(r, &obj);
	printf("  hts dequeue 1: %s (val=%lu)\n",
		ret == 0 ? "ok" : "fail", (uintptr_t)obj);

	ret = rte_ring_dequeue(r, &obj);
	printf("  hts dequeue 2: %s (val=%lu)\n",
		ret == 0 ? "ok" : "fail", (uintptr_t)obj);

	tla_trace_close();
	rte_ring_free(r);

	printf("  basic_hts done\n");
	return 0;
}

/* ================================================================
 * Main
 * ================================================================ */

int
main(int argc, char *argv[])
{
	int ret;

	ret = rte_eal_init(argc, argv);
	if (ret < 0) {
		fprintf(stderr, "EAL init failed: %s\n",
			rte_strerror(rte_errno));
		return 1;
	}
	argc -= ret;
	argv += ret;

	/* Override trace directory from env */
	const char *env_dir = getenv("TRACE_DIR");
	if (env_dir)
		trace_dir = env_dir;

	printf("Trace output: %s/\n", trace_dir);
	printf("Lcores available: %u\n", rte_lcore_count());

	ret = 0;
	ret |= test_basic_mpmc();
	ret |= test_concurrent_mpmc();
	ret |= test_basic_hts();

	rte_eal_cleanup();

	return ret ? 1 : 0;
}
