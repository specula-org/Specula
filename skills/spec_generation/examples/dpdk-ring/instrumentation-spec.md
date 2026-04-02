# Instrumentation Spec: DPDK rte_ring

Maps TLA+ spec actions to source code locations for trace harness generation.

## Section 1: Trace Event Schema

### Event Envelope

```json
{
  "event": "<action_name>",
  "thread": "<thread_id>",
  "n": <batch_size>,
  "commitN": <peek_commit_count>,
  "state": {
    "prodHead": <uint32>,
    "prodTail": <uint32>,
    "consHead": <uint32>,
    "consTail": <uint32>
  }
}
```

### State Fields

| Implementation field | TLA+ variable | Access |
|---------------------|---------------|--------|
| `r->prod.head` | `prodHead` | `rte_atomic_load(&r->prod.head)` |
| `r->prod.tail` | `prodTail` | `rte_atomic_load(&r->prod.tail)` |
| `r->cons.head` | `consHead` | `rte_atomic_load(&r->cons.head)` |
| `r->cons.tail` | `consTail` | `rte_atomic_load(&r->cons.tail)` |

For RTS mode, also capture:
| `r->rts_prod.head.val.cnt` | `prodCnt` | 64-bit atomic load, extract upper 32 bits |
| `r->rts_prod.tail.val.cnt` | `prodTailCnt` | 64-bit atomic load, extract upper 32 bits |

### Thread ID

Use `rte_lcore_id()` as the thread identifier string.

## Section 2: Action-to-Code Mapping

### ReserveProd

- **Spec action**: `MPMCReserveProd` / `HTSReserveProd` / `RTSReserveProd`
- **Code locations**:
  - MPMC: `rte_ring_elem_pvt.h:414-415` (`__rte_ring_move_prod_head`)
  - HTS: `rte_ring_hts_elem_pvt.h:216` (`__rte_ring_hts_move_prod_head`)
  - RTS: `rte_ring_rts_elem_pvt.h:231` (`__rte_ring_rts_move_prod_head`)
- **Trigger**: AFTER the move_head function returns (CAS succeeded)
- **Event name**: `"ReserveProd"`
- **Fields**: `thread`, `n` (return value from move_head), `state` (weak: prodHead, consHead)
- **Notes**: For MPMC, `n` comes from the return value. `old_head` is captured in `prod_head` local. State snapshot must be taken AFTER CAS succeeds.

### ReserveCons

- **Spec action**: `MPMCReserveCons` / `HTSReserveCons` / `RTSReserveCons`
- **Code locations**:
  - MPMC: `rte_ring_elem_pvt.h:461-462` (`__rte_ring_move_cons_head`)
  - HTS: `rte_ring_hts_elem_pvt.h:257` (`__rte_ring_hts_move_cons_head`)
  - RTS: `rte_ring_rts_elem_pvt.h:272` (`__rte_ring_rts_move_cons_head`)
- **Trigger**: AFTER the move_head function returns
- **Event name**: `"ReserveCons"`
- **Fields**: `thread`, `n`, `state` (weak: prodHead, consHead)

### WriteData

- **Spec action**: `WriteData`
- **Code locations**:
  - Enqueue: `rte_ring_elem_pvt.h:419` (`__rte_ring_enqueue_elems`)
  - Dequeue: `rte_ring_elem_pvt.h:466` (`__rte_ring_dequeue_elems`)
- **Trigger**: AFTER the copy function returns
- **Event name**: `"WriteData"`
- **Fields**: `thread`
- **Notes**: No state snapshot needed (ring positions unchanged during copy). The side (prod/cons) is inferred from the preceding Reserve event.

### PublishTail

- **Spec action**: `MPMCPublishTail` / `HTSPublishTail` / `RTSPublishTail`
- **Code locations**:
  - MPMC: `rte_ring_elem_pvt.h:421` → `rte_ring_c11_pvt.h:25-45` (`__rte_ring_update_tail`)
  - HTS: `rte_ring_hts_elem_pvt.h:220` → `rte_ring_hts_elem_pvt.h:26-43` (`__rte_ring_hts_update_tail`)
  - RTS: `rte_ring_rts_elem_pvt.h:235` → `rte_ring_rts_elem_pvt.h:24-62` (`__rte_ring_rts_update_tail`)
- **Trigger**: AFTER the update_tail function returns
- **Event name**: `"PublishTail"`
- **Fields**: `thread`, `state` (strong: all four positions)
- **Notes**: This is the linearization point. Full state snapshot is critical here.

### PeekStart

- **Spec action**: `PeekStartProd` / `PeekStartCons`
- **Code locations**:
  - Enqueue: `rte_ring_peek_elem_pvt.h:113-140` (`__rte_ring_do_enqueue_start`)
  - Dequeue: `rte_ring_peek_elem_pvt.h:146-177` (`__rte_ring_do_dequeue_start`)
- **Trigger**: AFTER the start function returns
- **Event name**: `"PeekStart"`
- **Fields**: `thread`, `n`, `state` (weak: prodHead, consHead)

### PeekFinish

- **Spec action**: `PeekFinish`
- **Code locations**:
  - ST: `rte_ring_peek_elem_pvt.h:52-63` (`__rte_ring_st_set_head_tail`)
  - HTS: `rte_ring_peek_elem_pvt.h:96-108` (`__rte_ring_hts_set_head_tail`)
- **Trigger**: AFTER the set_head_tail function returns
- **Event name**: `"PeekFinish"`
- **Fields**: `thread`, `commitN` (the `num` parameter), `state` (strong: all four positions)

### Stall

- **Spec action**: `Stall`
- **Code locations**: N/A (injected by test harness, not from application code)
- **Trigger**: Test harness injects a sleep/pause between Reserve and PublishTail
- **Event name**: `"Stall"`
- **Fields**: `thread`
- **Notes**: This is a fault-injection event. The test harness must emit this event when it deliberately stalls a thread (e.g., via `usleep()` or signal-based suspension).

## Section 3: Special Considerations

### Thread Interleaving

DPDK uses pinned-core polling, so each lcore runs one thread. Events from different lcores will interleave in the trace. The trace file must be written with proper synchronization (e.g., per-thread buffering + flush, or a global lock on the trace writer).

### Initial State

The trace should start after `rte_ring_create()` completes. The initial state is:
- `prodHead = prodTail = consHead = consTail = 0`
- All ring slots are empty

If the ring has been pre-populated, the first trace event should include the initial state in a special `"Init"` event.

### Mode Selection

The ring's sync mode is determined at creation time and doesn't change. The trace should include the mode in the first event or as a separate metadata event:
```json
{"event": "Init", "mode": "MPMC", "capacity": 3}
```

The Trace.cfg constants (Mode, Capacity) must match the actual ring configuration.

### RTS Counter Domain

For RTS mode traces, the counter values will be real uint32_t values that can grow very large. The Trace.tla should either:
1. Use the actual counter values (set CntMax high enough), or
2. Map counters modulo CntMax in the trace post-processing step

### Batch Size

The `n` field in Reserve events is the ACTUAL number of slots reserved (the return value), not the requested number. For `RTE_RING_QUEUE_VARIABLE` behavior, this may be less than requested.

### WriteData Elision

In high-performance scenarios, the WriteData event may be elided since it doesn't change ring metadata. The Trace.tla handles this by making WriteData a non-validating action (no post-state check). If elided, the base spec's WriteData action will fire as a silent action between Reserve and PublishTail.
