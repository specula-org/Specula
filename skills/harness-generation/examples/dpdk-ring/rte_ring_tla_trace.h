/* SPDX-License-Identifier: BSD-3-Clause
 * TLA+ trace emission for DPDK rte_ring.
 * Emits NDJSON events for trace validation against the ring spec.
 *
 * All functions are guarded by DPDK_TLA_TRACE — zero cost when disabled.
 */

#ifndef RTE_RING_TLA_TRACE_H
#define RTE_RING_TLA_TRACE_H

#ifdef DPDK_TLA_TRACE

#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <pthread.h>

/*
 * Forward declaration: struct rte_ring is defined in rte_ring_core.h,
 * which is always included before this header.
 */

/* ---- Thread-local thread ID ---- */
static __thread unsigned int __tla_tid;

static inline void
tla_trace_set_thread_id(unsigned int id)
{
	__tla_tid = id;
}

/* ---- Global trace writer (mutex-protected) ---- */
static FILE *__tla_fp __attribute__((unused));
static pthread_mutex_t __tla_mu = PTHREAD_MUTEX_INITIALIZER;

static inline void
tla_trace_open(const char *path)
{
	if (!path || !path[0])
		return;
	pthread_mutex_lock(&__tla_mu);
	if (!__tla_fp)
		__tla_fp = fopen(path, "w");
	pthread_mutex_unlock(&__tla_mu);
}

static inline void
tla_trace_close(void)
{
	pthread_mutex_lock(&__tla_mu);
	if (__tla_fp) {
		fflush(__tla_fp);
		fclose(__tla_fp);
		__tla_fp = NULL;
	}
	pthread_mutex_unlock(&__tla_mu);
}

/* ---- Real timestamp (monotonic nanoseconds) ---- */
static inline uint64_t
__tla_ts_ns(void)
{
	struct timespec ts;
	clock_gettime(CLOCK_MONOTONIC, &ts);
	return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

/* ---- State snapshot (mode-aware) ----
 *
 * The rte_ring union layout differs by sync mode:
 *   MPMC/HTS: prod.head at offset 0, prod.tail at offset 4
 *   RTS: rts_prod.tail at offset 0..7, rts_prod.head at offset 16..23
 *         (head and tail positions are at .val.pos within 64-bit poscnt)
 *
 * prod.tail at offset 4 is always the tail POSITION regardless of mode
 * (the struct comment says "offset for tail values should remain the same").
 * prod.head at offset 0 is correct for MPMC/HTS, but for RTS it overlaps
 * with rts_prod.tail.val.cnt (the tail's reference counter).
 */
static inline void
__tla_snap_state(const struct rte_ring *r,
		 uint32_t *ph, uint32_t *pt,
		 uint32_t *ch, uint32_t *ct)
{
	/* Tail position: always at consistent offset across modes */
	*pt = rte_atomic_load_explicit(&r->prod.tail,
				       rte_memory_order_relaxed);
	*ct = rte_atomic_load_explicit(&r->cons.tail,
				       rte_memory_order_relaxed);

	/* Head position: differs for RTS mode */
	if (r->prod.sync_type == RTE_RING_SYNC_MT_RTS) {
		union __rte_ring_rts_poscnt h;
		h.raw = rte_atomic_load_explicit(&r->rts_prod.head.raw,
						 rte_memory_order_relaxed);
		*ph = h.val.pos;
	} else {
		*ph = rte_atomic_load_explicit(&r->prod.head,
					       rte_memory_order_relaxed);
	}

	if (r->cons.sync_type == RTE_RING_SYNC_MT_RTS) {
		union __rte_ring_rts_poscnt h;
		h.raw = rte_atomic_load_explicit(&r->rts_cons.head.raw,
						 rte_memory_order_relaxed);
		*ch = h.val.pos;
	} else {
		*ch = rte_atomic_load_explicit(&r->cons.head,
					       rte_memory_order_relaxed);
	}
}

/* ---- Core emit function ---- */
static inline void
__tla_trace_emit_full(const char *event, const struct rte_ring *r,
		      int has_n, unsigned int n,
		      int has_commitN, unsigned int commitN)
{
	if (!__tla_fp)
		return;

	uint32_t ph, pt, ch, ct;
	__tla_snap_state(r, &ph, &pt, &ch, &ct);

	char buf[512];
	int off = 0;

	off += snprintf(buf + off, sizeof(buf) - off,
		"{\"tag\":\"trace\",\"ts\":\"%lu\","
		"\"event\":\"%s\",\"thread\":\"t%u\"",
		(unsigned long)__tla_ts_ns(), event, __tla_tid);

	if (has_n)
		off += snprintf(buf + off, sizeof(buf) - off,
			",\"n\":%u", n);
	if (has_commitN)
		off += snprintf(buf + off, sizeof(buf) - off,
			",\"commitN\":%u", commitN);

	off += snprintf(buf + off, sizeof(buf) - off,
		",\"state\":{\"prodHead\":%u,\"prodTail\":%u,"
		"\"consHead\":%u,\"consTail\":%u}}",
		ph, pt, ch, ct);

	pthread_mutex_lock(&__tla_mu);
	if (__tla_fp) {
		fprintf(__tla_fp, "%s\n", buf);
		fflush(__tla_fp);
	}
	pthread_mutex_unlock(&__tla_mu);
}

/* ---- Convenience emit functions (called from instrumented ring code) ---- */

static inline void
__tla_trace_reserve_prod(const struct rte_ring *r, unsigned int n)
{
	__tla_trace_emit_full("ReserveProd", r, 1, n, 0, 0);
}

static inline void
__tla_trace_reserve_cons(const struct rte_ring *r, unsigned int n)
{
	__tla_trace_emit_full("ReserveCons", r, 1, n, 0, 0);
}

static inline void
__tla_trace_write_data(const struct rte_ring *r)
{
	__tla_trace_emit_full("WriteData", r, 0, 0, 0, 0);
}

static inline void
__tla_trace_publish_tail(const struct rte_ring *r)
{
	__tla_trace_emit_full("PublishTail", r, 0, 0, 0, 0);
}

static inline void
__tla_trace_peek_start(const struct rte_ring *r, unsigned int n)
{
	__tla_trace_emit_full("PeekStart", r, 1, n, 0, 0);
}

static inline void
__tla_trace_peek_finish(const struct rte_ring *r, unsigned int commitN)
{
	__tla_trace_emit_full("PeekFinish", r, 0, 0, 1, commitN);
}

static inline void
__tla_trace_stall(const struct rte_ring *r)
{
	__tla_trace_emit_full("Stall", r, 0, 0, 0, 0);
}

#else /* !DPDK_TLA_TRACE */

/* Stubs — zero cost when tracing is disabled */
static inline void tla_trace_set_thread_id(unsigned int id) { (void)id; }
static inline void tla_trace_open(const char *p) { (void)p; }
static inline void tla_trace_close(void) {}

#endif /* DPDK_TLA_TRACE */
#endif /* RTE_RING_TLA_TRACE_H */
