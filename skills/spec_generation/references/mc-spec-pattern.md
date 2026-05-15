# MC Spec Pattern

Template and methodology for writing model checking specs that wrap the base spec with counter-bounded actions.

> **On examples**: any examples below are historical instances from specific case studies. They illustrate mechanics, not models to imitate. Your target's wrappers should come from your target's code, not from copying these.

> **Category vocabulary** — fault-family vocabulary is in `code_analysis/references/distributed-analysis.md`, `concurrent-analysis.md`, and `bft-analysis.md`. Use it as shorthand in the modeling brief; do not treat the family lists as a checklist that every target must cover.

## Purpose

The MC spec enables exhaustive state space exploration by bounding non-deterministic actions, adding symmetry reduction, and defining structural invariants and temporal properties.

## Structure

1. **EXTENDS base spec** + `INSTANCE base` for original operator access (needed because cfg overrides operators)
2. **Counter variables** — one counter per fault-injection action, stored in a single record
3. **Constrained wrappers** — guard + original action + counter increment
4. **Unconstrained actions** — deterministic/reactive actions pass through with `UNCHANGED faultVars`
5. **MCInit** — base Init + counter initialization
6. **MCNext** — all wrappers grouped (async per-server actions, crash actions, message actions)
7. **Symmetry and view** — `Permutations(Server)`, exclude counters from view
8. **State space pruning** — message buffer constraint
9. **Invariants and temporal properties**

## Which Actions to Bound

**Bound**: actions that *introduce* non-determinism (timeout, client request, crash, message loss, heartbeat, disk block, config change).

**Don't bound**: actions that *react* to existing state (message handlers, become leader, advance commit index, complete persist, drop stale message).

For **Category B** systems:

- **Bound** the injected bug mechanism: stale snapshot capture, skipped re-check, premature reclaim, wrong wakeup, weakened ordering bridge, buggy fallback path
- **Do not bound away** the normal reactive steps that make the bug reachable: publish, confirm, help-transfer, reclaim scan, wakeup completion
- Prefer **2-3 threads**, very small capacities / buffer sizes / key sets, and tiny bounds on unrelated actions so the target interleaving remains reachable

## Fault Family Wrappers — Guidance, Not Templates

Fault family vocabulary (e.g., "crash / loss / timeout / cancellation / OOM / caller misuse") lives in `code_analysis/references/*-analysis.md`. Those names are available as shorthand for organising the modeling brief — use them when they help; ignore them when they don't fit.

**Wrapper design is case-specific.** Derive each adversary action from concrete code evidence in YOUR target — what is the actual mechanism, what state can the implementation reach, what observable effect does it produce? Do **not** copy wrapper names, counter shapes, or schematic templates verbatim from existing case studies; their design decisions reflect those targets' specific code, and mechanical reuse propagates problems. (Concrete example we've seen go wrong: a wrapper named `MCSkipReaderFence` in one of the older specs models removing an existing SeqCst fence — that's `git revert` in spec form, which produces no information beyond what the closed PR already records.)

A few mechanics that are usually universal:

- Each fault-injection action takes a per-action counter to bound its firing rate. Counter must be checked AND incremented on the same transition; otherwise the "bounded" fault fires forever.
- Reactive actions (message handlers, state advancement, completion of in-flight operations) should not be bounded — only the actions that *introduce* non-determinism are.
- The base spec's action granularity is decided in `base.tla`; the MC layer should not silently merge or split actions to manage state space.

Beyond those mechanics, the right question is not "which family am I checking off?" but "what concrete, open question about my target am I trying to answer?" If you cannot articulate a concrete open question — not anchored to any past commit, fix, or known PR — then there is probably no wrapper worth writing for that family in this case. See `bug-archaeology.md` § 1.4 and `modeling-brief-format.md` § 6.1 for the value-driven principle that constrains which wrappers are worth writing.

If a target has a domain-specific fault that isn't named in any taxonomy file, model it directly. The taxonomy is a vocabulary, not a definition of "fault model".

## Config Pattern

Use operator overrides (`<-`) to inject counter constraints:

```
Timeout       <- MCTimeout
Crash         <- MCCrash
ClientRequest <- MCClientRequest
...
```

## Tuning Constants

Start in the 2-8 range per constant. Too small misses bugs; increase one constant at a time if needed. State space grows exponentially.

| Constant | Recommended | Notes |
|----------|-------------|-------|
| MaxTermLimit | 4 | Most bugs manifest within 3-4 terms |
| MaxTimeoutLimit | 5 | Multiple elections needed for some bugs |
| RequestLimit | 3 | Log entries for commit advancement |
| CrashLimit | 2 | Crash-recovery bugs need at least 1 |
| LoseLimit | 3 | Network partition simulation |
| HeartbeatLimit | 6 | Lease/contact bugs need multiple heartbeats |
| MaxMsgBufferLimit | 8-12 | Too low prunes valid states |

## Hunting Configs

Generate one `MC_hunt_<family>.cfg` per bug family from the modeling brief. These are used **after spec convergence** to find real bugs.

**Naming**: `MC_hunt_<family>.cfg` or `MC_family<N>.cfg` (match the bug family name/number from the brief).

**Pattern** — differ from `MC.cfg` in two ways:

1. **Tight bounds**: reduce irrelevant action limits to 0-1, keep only the limits that trigger the target bug mechanism
2. **Targeted invariants**: only the bug-family invariant + core safety. Do not include structural invariants or other families' invariants

**MC.cfg invariant organization**: group invariants by category with comments, and **comment out** extension (bug-family) invariants.

**Examples**:
- Standard MC.cfg: `../examples/braft/MC.cfg` (standard + structural invariants, bug-detection commented out)
- Hunting cfg (tight bounds): `../examples/braft/MC.cfg` (crash-recovery family, minimal bounds)
- Hunting cfg (targeted invariant): `../examples/cometbft/MC.cfg` (VE liveness, zeroed irrelevant limits)

### Category B Hunting Pattern

For concurrent / lock-free systems, a good hunting config usually has:

1. **One mechanism only** — e.g. stale head, premature reclaim, skipped re-check
2. **Tiny structure bounds** — capacity 2-3, 1-3 keys/values, 2-3 threads
3. **Real bad-state invariants** — no use-after-free, no double-consume, no lost element, no over-capacity, no parked-on-aborted
4. **Irrelevant actions near zero** — but keep the target mechanism and its enabling interleavings alive

Do **not** make BFS deeper by shrinking the target mechanism itself. Shrink unrelated actions first.

## Example

See `../examples/cometbft/MC.tla` and `../examples/cometbft/MC.cfg` for a complete MC spec with counter-bounded actions, structural invariants, and temporal properties.
