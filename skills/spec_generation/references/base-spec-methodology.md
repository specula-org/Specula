# Base Spec Methodology

How to write a TLA+ base spec from a Modeling Brief.

> **Note**: Examples reference Raft (hashicorp/raft) as an illustrative case study. Adapt to your target system. For Category B systems, the right template is often thread-local state + shared memory windows, not messages and roles.

> **Category routing** — sections in this file are split by target category:
> - **Category A** (distributed) → § "Action Design / When to Split" (general) + § "Fault Injection / Category A" (canonical fault actions: Crash, LoseMessage, Partition, Timeout) + § "Crash and Recovery". Bug-class taxonomy in `code_analysis/references/distributed-analysis.md` § 5.
> - **Category B** (concurrent / lock-free) → § "Granularity for Concurrent Specs" (the headline 5.1) + § "Fault Injection / Category B" (5.2-5.8 fault action shapes). Bug-class taxonomy in `code_analysis/references/concurrent-analysis.md` § 5.
>
> Sections "Variable Design", "Action Design / Naming / Structure", "Invariant Design", "Helpers" apply to both categories.

## Principle: Bug-Family Driven, Code-Faithful

The spec's **scope** is driven by Bug Families — what variables to add, how to split actions, what invariants to check. But the **logic** within each action must faithfully follow the implementation's actual control flow. For the code paths we model, the spec must match the implementation's conditions, branches, and state updates precisely.

**Every logic block within an action must be annotated with source code line references.**

## Variable Design

Start from standard protocol variables, then add **extension variables** from Bug Families. Every extension variable must cite which Bug Family motivates it and what code it models.

Group variables for UNCHANGED clauses (e.g., `serverVars`, `logVars`, `leaderVars`).

For **Category B** systems, common extension variables include:

- per-thread / per-task PC state
- cached snapshots of shared pointers / indices / counters
- reservation vs publication state
- retire / reclaim queues or epochs
- ownership-transfer flags
- helping / fallback / wakeup state

## Action Design

### Naming

Name actions after implementation functions (e.g., `HandleRequestVoteRequest`, not `HandleRV`).

### When to Split

Split a single implementation function into multiple spec actions when:
1. **Different code paths have different checks** — e.g., one response path checks `resp.Term` while another skips it
2. **Non-atomic operations have crash windows** — e.g., persistence writes term then votedFor separately
3. **Independent threads/goroutines have different properties** — e.g., heartbeat runs without disk access while replicate requires disk
4. **A lock-free operation has separate visibility stages** — e.g., read snapshot -> confirm -> dereference, reserve -> write -> publish, retire -> reclaim
5. **Ownership transfers across threads** — e.g., enqueue wakeup -> decrement counter -> complete, detach -> fulfill -> bottom-half finish

### Granularity for Concurrent Specs — *the headline fault family*

For concurrent / lock-free targets, action granularity is the most important faithfulness decision in the entire spec. Production concurrent bugs are overwhelmingly pure interleaving bugs — two correct-looking operations run in an order the author did not consider — and TLC is uniquely good at exposing them by exhaustively exploring all interleavings. A spec that collapses a multi-step protocol into one atomic action makes those bugs invisible, no matter how careful the rest of the spec is.

The adversary here is **already present** in TLA+'s default interleaving semantics. You do not add it with an `MCPreempt` action — you express it through how you split actions in the first place.

**Wrong (collapsed)** — `load → check → CAS` as one action:

```tla
PushNode(t, n) ==
    /\ shared.head /= NULL_PTR
    /\ shared' = [shared EXCEPT !.head =
                    IF @ = pcLocal[t].observed THEN n ELSE @]
```

Every interleaving where another thread mutates `shared.head` between the load and the CAS is hidden.

**Right (split)** — three actions, one per atomic step:

```tla
PushLoad(t) ==
    /\ pcLocal[t].step = "ready"
    /\ pcLocal' = [pcLocal EXCEPT ![t] = [step |-> "loaded",
                                          observed |-> shared.head]]
    /\ UNCHANGED shared

PushCheck(t) ==
    /\ pcLocal[t].step = "loaded"
    /\ ... \* validation logic
    /\ pcLocal' = [pcLocal EXCEPT ![t].step = "ready_to_cas"]

PushCAS(t) ==
    /\ pcLocal[t].step = "ready_to_cas"
    /\ shared.head = pcLocal[t].observed   \* CAS expected check
    /\ shared' = [shared EXCEPT !.head = pcLocal[t].newNode]
    /\ pcLocal' = [pcLocal EXCEPT ![t].step = "ready"]
```

Each action boundary is an interleaving point. TLC explores every order across these boundaries.

**Granularity audit** — when reviewing or generating a base spec, walk every action and ask:

| Question | If "yes" → split the action |
|---|---|
| Does it contain more than one atomic operation that another thread can observe between? | Yes |
| Does the implementation release a lock or yield within this action? | Yes |
| Does it span an `await` / `co_await` / `.await` point? | Yes |
| Does it perform `load → conditional → store` where the load result feeds the store? | Yes |
| Is it a single CAS, single atomic load, or single atomic store? | No (already correct) |
| Does the implementation hold a single lock across the whole action with no release? | No (atomic by construction) |

State-space cost is real, but control it through **counter bounds, scenario configs, and symmetry reduction in the MC layer** — not by collapsing actions in the base spec. Collapsing for state-space reasons is a faithfulness regression that silently kills bug-finding power and is much harder to detect than an explicit bound.

See `code_analysis/references/concurrent-analysis.md` § 5.1 for the bug-class reasoning that motivates this.

### Action Structure

Each action follows this pattern:
- Action-level comment cites the overall function (`file:line-range`)
- Every logic block inside (branches, LET bindings, conditions) cites specific source lines
- Each case in a disjunction has a descriptive comment

### Message Types

Use descriptive constants. Include a `msubtype` field when the same RPC type has different code paths (e.g., "heartbeat" vs "replicate" for AppendEntries).

## Invariant Design

Three categories:
1. **Standard protocol invariants** — fundamental safety properties
2. **Extension invariants** — target specific Bug Families (primary bug-detection tools)
3. **Structural invariants** — sanity checks that hold in all correct states

## Helpers

Common patterns: log entry records with type fields, message bags (Send/Discard/Reply using Bags module), configuration helpers for dual-config modeling.

## Fault Injection

This section defines the fault **actions** — the state transitions the adversary can take. The MC spec wraps these with counter bounds; see `mc-spec-pattern.md`. Both layers are needed: the base spec describes what the adversary can do, the MC spec bounds how often.

System-specific fault actions take priority over generic ones. The analysis report's Bug Families should drive the action set — examples: disk IO blocking (heartbeat continues while replicate stalls), non-atomic persistence (crash between two disk writes), configuration change mid-election. Design fault-injection actions based on what the Bug Families identify, not just common fault categories.

### Category A (Distributed) — canonical fault actions

- `Crash(s)` — server stops; in-memory state lost, persisted state retained
- `LoseMessage(m)` — message removed from network bag
- `PartitionServer(s)` — server isolated from network
- `Timeout(s)` — election / leader / liveness timer fires
- Plus any system-specific fault actions surfaced by Bug Families (disk IO blocking, non-atomic persist windows, mid-election config change, etc.)

### Category B (Concurrent / Lock-Free) — by fault family

The fault family taxonomy lives in `code_analysis/references/concurrent-analysis.md` § 5 — that file decides which families apply to which sub-categories. Do not duplicate the list here.

For each family that applies, define the underlying fault action in this base spec; the MC layer adds the counter wrapper:

| Family | Action shape in base spec |
|---|---|
| 5.1 Thread interleaving | Not a fault action — handled via action granularity (see "Granularity for Concurrent Specs" above) |
| 5.2 Cancellation | `DropFuture(t)`, `CloseChannel`, `CancelTask(t)` |
| 5.3 OOM | `AllocFail(site)` driving the allocation site to its error branch |
| 5.4 CAS_weak | tag CAS as weak/strong; weak CAS gets a `SpuriousFail` disjunct |
| 5.5 MemOrder | actions for cross-variable visibility bridges (e.g., `StaleRead(t)`, `SkipFence(r)`) |
| 5.6 ABA | reclamation returns slot/generation to free pool; CAS uses `(ptr, gen)` tuple |
| 5.7 Caller misuse | external `ClientHarness` action set with adversarial call sequences |
| 5.8 Lost wakeup | `SpuriousWake(t)` transitions a parked thread to ready without `Notify` |

System-specific fault actions outside 5.1-5.8 (e.g., NIC packet reorder, signal-during-RMW, JIT barrier reordering) are equally first-class — add them when the analysis identifies them. The eight families are starting points, not a constraint.

## Crash and Recovery

For non-atomic persistence: after crash, in-memory state reverts to persisted state (which may differ if a non-atomic persist was interrupted).

## Example

See `../examples/cometbft/base.tla` for a complete base spec with extensions, full source line annotations, and action splitting.
