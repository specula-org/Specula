# MC Spec Pattern

Template and methodology for writing model checking specs that wrap the base spec with counter-bounded actions.

> **Note**: Examples reference Raft as an illustrative case study. Adapt action names, constants, and bounds to your target system. Category B systems usually need fewer threads and smaller structures, but finer-grained actions and more targeted fault injection.

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
