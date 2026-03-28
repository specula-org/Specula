# Trace Spec Pattern

Template and methodology for writing trace validation specs.

> **Note**: Examples reference Raft (hashicorp/raft) as an illustrative case study. Adapt event names, state fields, and action wrappers to your target system.

> **Important**: There are two trace spec patterns depending on system category. See the harness-generation skill's `guide.md` Step 0 for classification.
> - **Category A (Distributed/Message-Passing)**: Single-file linear trace. Use the standard pattern below.
> - **Category B (Concurrent/Lock-Free)**: Per-thread timebox trace. Use the timebox pattern at the end of this document.

---

## Category A: Standard Trace Spec (Distributed Systems)

## Purpose

The trace spec drives TLC through a recorded execution trace from the real implementation, verifying that the base spec can reproduce every observed state transition.

**The trace spec validates ALL base spec logic.** Do not skip or weaken action logic unless the skipped logic has zero value for bug detection. Every action wrapper should call the full base spec action and validate the complete post-state. Skipping checks defeats the purpose of trace validation — finding where the spec and implementation disagree.

## Structure

1. **Trace loading** — `ndJsonDeserialize` from JSON file, filter by tag
2. **Cursor variable** `l` — walks through trace events; `logline == TraceLog[l]`
3. **Role/type mapping** — implementation strings to spec constants
4. **Server extraction** — derive Server set from trace
5. **Event predicates** — `IsEvent(name)`, `IsNodeEvent(name, i)`, `IsMsgEvent(name, from, to)`
6. **Post-state validation** — verify spec state matches trace after each action
7. **Action wrappers** — match event → call base action → validate → `l' = l + 1`
8. **Silent actions** — fire base actions without consuming a trace event
9. **TraceNext** — all wrappers + silent actions
10. **TraceMatched** — temporal property checking entire trace was consumed

## Silent Actions

Silent actions handle impl state changes without trace events (e.g., leader noop append, concurrent timeouts). **Unconstrained silent actions cause state space explosion.** Always add preconditions:
- Check `l <= Len(TraceLog)`
- Match against the *next* trace event that would require this silent action
- Restrict to specific nodes/states

## Granularity Mismatch: One Trace Event, Multiple Spec Steps

Sometimes the base spec models an operation as N sequential steps (each with its own PC state), but the trace can only observe the operation's start/end — not the intermediate steps.

**Always instrument each step separately so the trace has N events.** This gives full precondition checking at every intermediate state. Do not skip steps or combine them — the intermediate states are where subtle bugs hide.

If instrumenting individual steps is truly impossible (e.g., the code path is in an opaque library with no hook points), two weaker alternatives exist, but exhaust all instrumentation options first:

- Use N-1 silent actions for intermediate steps, with only the boundary step consuming the trace event
- Combine into a composite action, but document why each skipped precondition is not valuable to check

## Post-State Validation

**Strong validation**: check term, role, commitIndex, lastLogIndex, lastLogTerm — for actions where trace records full state.

**Weak validation**: check only term + role — for async actions where trace may not capture full state.

## Bootstrap State

TraceInit must match the implementation's initial state, which may differ from the base spec's Init (e.g., initial term, bootstrap log entries).

## Trace.cfg Must Include TraceMatched

`Trace.cfg` must have `PROPERTIES TraceMatched` (uncommented). Without it, TLC reports "no errors" even when `l` never advances — trace validation becomes a false positive. Define `TraceMatched == <>(l > Len(TraceLog))` in `Trace.tla` and include `PROPERTIES TraceMatched` in `Trace.cfg`.

## Common Issues

| Issue | Solution |
|-------|----------|
| TraceMatched violated at line N | Event N cannot match any base spec action |
| Deadlock at line N | No enabled action for event N |
| TLC never finishes | Unconstrained silent action causing infinite branching |
| State mismatch after action | Post-state validation failed — spec and impl disagree |
| Message not found in bag | Already consumed by silent action or prior event |

## Example

See `case-studies/hashicorp-raft/scenarios/base/spec/Tracehashiraft.tla` and `Tracehashiraft.cfg` for a complete trace spec with 11 action wrappers, 3 silent actions, bootstrap state, and strong/weak validation.

---

## Category B: Timebox Trace Spec (Concurrent/Lock-Free Systems)

For concurrent and lock-free data structures (DPDK ring, arc-swap, libomp, crossbeam-epoch) where operations are ns-level. Uses per-thread traces with `[start, end]` intervals instead of a single global trace sequence.

### Key Differences from Category A

| Aspect | Category A | Category B |
|--------|-----------|-----------|
| Trace variable | `l` (single cursor) | `pc` (per-thread cursor: `[Thread -> Nat]`) |
| Logline access | `TraceLog[l]` | `traces[tid][pc[tid]]` |
| Advance | `l' = l + 1` | `pc' = [pc EXCEPT ![tid] = pc[tid] + 1]` |
| Event ordering | Fixed (file order) | Partial order (TLC searches via `ViablePIDs`) |
| Completion check | `l > Len(TraceLog)` | `ThreadsWithEvents = {}` |
| Trace format | Single NDJSON file | Preprocessed JSON with per-thread arrays |

### Structure

1. **Trace loading** — `JsonDeserialize` from preprocessed JSON (per-thread arrays with compressed timestamps)
2. **Per-thread cursor** `pc` — `[Thread -> Nat]`, each thread's index into its trace
3. **ThreadsWithEvents** — threads that still have unconsumed events
4. **ViablePIDs** — partial order constraint: thread can step iff no other thread has a pending event that completed before this thread's next event started
5. **Event matching** — `MatchEvent(tid, logline)`: dispatch by event name, validate state, call base action
6. **Silent actions** — same as Category A, fire without advancing any `pc`
7. **TraceNext** — `\E tid \in ViablePIDs : MatchEvent(...)` + silent actions + stuttering
8. **TraceFullyConsumed** — temporal property `<>(ThreadsWithEvents = {})`

### ViablePIDs (Core Concept)

```tla
ViablePIDs ==
    { tid \in ThreadsWithEvents :
        ~ \E tid2 \in ThreadsWithEvents :
            /\ tid2 /= tid
            /\ traces[tid2][pc[tid2]].end < traces[tid][pc[tid]].start }
```

If thread A's pending event **ended before** thread B's next event **started**, then A must go first (B is not viable yet). If intervals overlap, both are viable — TLC explores both orderings.

### State Validation

State is still captured and validated (unlike pure OmniLink which drops state). State is captured **outside** the `[start, end]` interval to keep it tight. The captured state corresponds to the real execution ordering, so at least one TLC-explored interleaving will match.

State mismatches on non-real orderings cause those branches to die — this is pruning, not a problem.

### TraceNext Pattern

```tla
TraceNext ==
    \/ /\ ThreadsWithEvents /= {}
       /\ \E tid \in ViablePIDs :
            LET logline == traces[tid][pc[tid]] IN
            /\ MatchEvent(tid, logline)
            /\ pc' = [pc EXCEPT ![tid] = pc[tid] + 1]
    \/ /\ ThreadsWithEvents /= {}
       /\ SilentActions
       /\ UNCHANGED pc
    \/ /\ ThreadsWithEvents = {}
       /\ UNCHANGED <<vars, pc>>
```

### Do NOT Bypass Base Spec Actions

In Category B, TLC explores multiple interleavings. Some interleavings will cause a base spec action's precondition to fail (e.g., another thread modified shared state in this interleaving). This is **expected and correct** — those branches die, and TLC continues searching other interleavings.

**Always call the base spec action directly.** The real execution ordering is always among the viable orderings (because real execution times fall within the recorded intervals). In the real ordering, the spec state matches what the thread observed, so the base spec action will succeed. TLC is guaranteed to find this path.

Bypassing the base spec action (manually setting variables instead of calling the action) is **harmful**:
- It skips the base spec's precondition checks, weakening validation
- It allows dead branches to survive longer (dying at a later action instead of earlier), wasting TLC search time
- It risks accepting invalid traces that violate the spec

**Lesson from crossbeam-deque**: The initial implementation bypassed `StealBegin(tid)` with manual variable assignments. Review showed this was unnecessary — TLC's exhaustive search finds the correct interleaving where the base spec action succeeds. The bypass should be removed.

### Invariant Selection for Trace Validation

Not all MC invariants belong in Trace.cfg. Choose based on what trace validation can meaningfully check:

| Include in Trace.cfg | Reason |
|---|---|
| **Safety invariants** (ConsumedWasPushed, NoDoublePop, AgreementSafety) | Core correctness — should hold on every real execution |
| **Structural invariants** (DequeConsistency, CurrentBufferAlive, PushedDistinct) | Catches spec modeling errors early, before MC |

| Exclude from Trace.cfg | Reason |
|---|---|
| **Fault-injection invariants** (NoUseAfterFree with prematureReclaim) | Only meaningful when fault injection is active; traces run without faults |
| **Liveness/temporal properties** | Trace validation uses deadlock-based completion, not fairness |

**Rule of thumb**: If an invariant can be violated by a correct execution (e.g., requires fault injection to trigger), don't check it during trace validation. If it should hold on every real execution, check it.

### Search Space Control

Timebox traces create branching at every overlapping interval pair. Control via:
- **Tight intervals** (use `refine_op_start/end` around critical section)
- **Short traces** (50-300 events per trace, run many traces)
- **State validation** (prunes impossible orderings early)
- **Timestamp compression** (preprocessor maps raw rdtsc to dense integers)

### Example

See `harness-generation` skill's `references/concurrent-timebox-guide.md` for the full Trace.tla template, preprocessor script, and instrumentation patterns.

See `case-studies/crossbeam-deque/` for a complete Category B case study with ViablePIDs and 4 validated traces.

### Related Work

- **OmniLink** (Hackett et al., 2026): Timebox + linearizability, no state capture
- **CONVEROS** (Tang et al., ATC'25): Missing event markers, alternative for OS kernel modules
