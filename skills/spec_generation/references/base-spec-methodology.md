# Base Spec Methodology

How to write a TLA+ base spec from a Modeling Brief.

> **On examples**: any examples below (Raft, hashicorp/raft, cometbft, etc.) are historical instances illustrating mechanics. They are not models to imitate. Adapt to your target system; for Category B targets the right shape is usually thread-local state + shared memory windows rather than messages and roles.

> **Category vocabulary** — fault-family vocabulary lives in `code_analysis/references/distributed-analysis.md`, `concurrent-analysis.md`, and (for BFT) `bft-analysis.md`. Use it as shorthand when it helps; do not treat any family list as a checklist that every target must cover.

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

This section defines the fault **actions** — state transitions the adversary can take. The MC spec wraps these with counter bounds (see `mc-spec-pattern.md`). The base spec describes what the adversary can do; the MC spec bounds how often.

**Design fault-injection actions based on what your Bug Families actually identify, not on common fault categories or other case studies' lists.** System-specific fault actions take priority — disk IO blocking, non-atomic persist windows, mid-election config change, NIC packet reorder, signal-during-RMW, JIT barrier reordering, etc. — whatever the target's code and the open question demand. The fault-family vocabularies in `distributed-analysis.md`, `concurrent-analysis.md`, and `bft-analysis.md` are starting points for naming, not a constraint on design.

A reminder applicable to all categories: if you can characterise a fault action's effect as "equivalent to `git revert <commit>`" for some past commit — drop it. The MC run produces no information the closed PR didn't already record. See `mc-spec-pattern.md` § "Fault Family Wrappers — Guidance, Not Templates".

## Crash and Recovery

For non-atomic persistence: after crash, in-memory state reverts to persisted state (which may differ if a non-atomic persist was interrupted).

## Example

See `../examples/cometbft/base.tla` for a complete base spec with extensions, full source line annotations, and action splitting.
