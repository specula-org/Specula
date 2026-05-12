# MC Spec Pattern

Template and methodology for writing model checking specs that wrap the base spec with counter-bounded actions.

> **Note**: Examples reference Raft as an illustrative case study. Adapt action names, constants, and bounds to your target system. Category B systems usually need fewer threads and smaller structures, but finer-grained actions and more targeted fault injection.

> **Category routing** — sections in this file are split by target category:
> - **Category A** (distributed: Raft / Paxos / replicated storage / network FSM / streaming) → § "Applying Fault Families (Distributed Specs)"; bug-class taxonomy in `code_analysis/references/distributed-analysis.md` § 5. If the target is BFT, also see `code_analysis/references/bft-analysis.md` § 5 for Byzantine wrapper shapes — treat the template there as a starting skeleton, adapt to the target protocol's actual message schema and validation path.
> - **Category B** (concurrent / lock-free: lock-free data structures / synchronization primitives / runtimes / channels / collections) → § "Applying Fault Families (Concurrent Specs)"; bug-class taxonomy in `code_analysis/references/concurrent-analysis.md` § 5.
>
> Sections "Purpose", "Structure", "Which Actions to Bound", "Config Pattern", "Tuning Constants", "Hunting Configs" apply to both categories.

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

## Applying Fault Families (Distributed Specs)

Companion to `code_analysis/references/distributed-analysis.md` § 5. That file describes which fault families a distributed system needs; this section shows the spec-level patterns. Distributed bugs typically require **two or three families composed** (crash + persistence, partition + timeout, etc.) — see distributed-analysis.md § 5 "Composition" for combinations. For BFT targets, the Byzantine wrapper shapes in `bft-analysis.md` § 5 compose with the families below; consult both, and let the case-study evidence dictate which compositions to actually model — do not feel obligated to enable every wrapper that appears in either reference.

### 5.1-5.6 Spec Patterns by Family

| Family | Counter / mechanism | Wrapper shape | Existing reference |
|---|---|---|---|
| 5.1 Crash + Recovery | `cCrash < MaxCrashes` | `MCCrash(s) == /\ cnt < bound /\ Crash(s) /\ cnt' = cnt + 1` — base splits state into persistent + in-memory | `case-studies/cometbft/spec/MC.tla` (`MCCrash`); `case-studies/etcd-raft/spec/MC.tla` (`MCCrash`); `case-studies/mongodb-raftmongo/spec/MC.tla` (`MCCrash`) |
| 5.2 Loss / Partition / Reorder | `cLose < MaxLose`, `cPartition < MaxPartition` | `MCLoseMessage(m) == /\ cnt < bound /\ LoseMessage(m) /\ cnt' = cnt+1`; same shape for `MCPartitionServer(s)` | `case-studies/etcd-raft/spec/MC.tla` (`MCLoseMessage`, `MCPartitionServer`); `case-studies/cometbft/spec/MC.tla` (`MCLoseMessage`) |
| 5.3 Timeout | `cTimeout < MaxTimeout` | `MCTimeout(s) == /\ cnt < bound /\ Timeout(s) /\ cnt' = cnt + 1`; multiple per-stage timeouts allowed | `case-studies/cometbft/spec/MC.tla` (`MCHandleTimeoutPropose` / `MCHandleTimeoutPrevote` / `MCHandleTimeoutPrecommit`); `case-studies/aptosbft/spec/MC.tla` (`MCSignTimeout`) |
| 5.4 Non-Atomic Persistence | `cCrashPersist < MaxCrashPersist` | `MCCrashBetweenSignAndPersist(s) == /\ cnt < bound /\ CrashBetweenSignAndPersist(s) /\ cnt' = cnt + 1` — base must split persist into N sub-actions | `case-studies/aptosbft/spec/MC.tla` (`MCCrashBetweenSignAndPersist`) |
| 5.5 Configuration / Membership Change | `cConfig < MaxConfigChange` | `MCConfigChange(s, newCfg) == /\ cnt < bound /\ ConfigChange(s, newCfg) /\ cnt' = cnt + 1` | `case-studies/aptosbft/spec/MC.tla` (`MCEpochChange`) |
| 5.6 Snapshot / Catchup | `cSync < MaxSync` | `MCInstallSnapshot(s, snap) == /\ cnt < bound /\ InstallSnapshot(s, snap) /\ cnt' = cnt + 1`; or `MCTriggerSync(s)` for sync-trigger style | `case-studies/aptosbft/spec/MC.tla` (`MCTriggerSync`); `case-studies/etcd-raft/scenarios/snapshot/spec/MC.tla` |

System-specific fault actions (disk silent corruption, custom WAL truncation, leader lease drift, etc.) take counter-bounded wrappers in the same shape; pick a name that matches the underlying base action.

### Composition Bounds

Distributed bugs typically need 2-3 families simultaneously active. Set conservative initial bounds (1-2 each) and increase only the bound load-bearing for the bug family being hunted:

| Pair | Why it composes |
|---|---|
| `MaxCrashes + MaxLose` | crash during partial replication |
| `MaxCrashes + MaxCrashPersist` | partial fsync window |
| `MaxPartition + MaxTimeout` | classic split-brain |
| `MaxConfigChange + MaxCrashes` | lost commit during reconfig |

### Coverage Annotation

When generating MC.tla for a distributed target, document fault model coverage in the header so reviewers can verify it against `distributed-analysis.md` § 5 (and, for BFT targets, also against `bft-analysis.md` § 2 adversary categories):

```tla
\* Fault model coverage:
\*   5.1 Crash:               MCCrash with persistent vs in-memory state split
\*   5.2 Network:             MCLoseMessage + MCPartitionServer
\*   5.3 Timeout:             MCHandleTimeoutPropose / MCHandleTimeoutPrevote / MCHandleTimeoutPrecommit
\*   5.4 NonAtomicPersist:    skipped (target uses single-atomic-write fsync)
\*   5.5 ConfigChange:        skipped (cluster size fixed at boot)
\*   5.6 Snapshot:            n/a (no log compaction in scope)
```

If the target has a domain-specific fault not in 5.1-5.6 (e.g., GPS clock drift, geo-replication fan-out), add a row in the coverage block. The six families are starting points, not a definition of "fault model".

## Applying Fault Families (Concurrent Specs)

Companion to `code_analysis/references/concurrent-analysis.md` § 5. That file describes which fault families a concurrent system needs; this section shows the spec-level patterns for each. The **5.1 family (thread interleaving / action granularity)** is the universal headline and gets the most space; the other seven are situational — choose them based on the sub-category prioritization table in that reference.

### 5.1 Thread Interleaving — handled in the base spec, not here

5.1 is **not** an MC-wrapper concern. It is a base-spec design decision: how finely you split actions in the first place. See `base-spec-methodology.md` § "Granularity for Concurrent Specs" for the full pattern (wrong-vs-right examples, granularity audit checklist, anti-collapse discipline).

The MC layer's contribution to 5.1 is purely negative: do **not** silently collapse actions in MC wrappers to control state space. If the base spec splits a protocol into three actions, the MC wrapper must wrap each separately. Use counter bounds, scenario configs, and symmetry — described later in this file — to control state space without changing atomicity.

### 5.2-5.8 Spec Patterns by Family

| Family | Counter / mechanism | Wrapper shape | Existing reference |
|---|---|---|---|
| 5.2 Cancellation | `cDropFuture < MaxDropFuture` | `MCDropFuture(t) == /\ cnt < bound /\ DropFuture(t) /\ cnt' = cnt+1` | `case-studies/kanal/spec/MC.tla` (`MCDropRecvFutureCancel`, `MCDropSendFutureCancel`) |
| 5.3 OOM | `cAllocFail < MaxAllocFail` per site | `MCAllocFail(site) == /\ cAllocFail[site] < MaxAllocFail /\ AllocFail(site) /\ cAllocFail' = [cAllocFail EXCEPT ![site] = @ + 1]` drives error branch | None yet — universally unmodeled |
| 5.4 CAS_weak | `cSpuriousFail < MaxSpurious` | `MCCASWeakFail(t) == /\ cSpuriousFail < MaxSpurious /\ CASExpectedMatch(t) /\ CASFail(t) /\ cSpuriousFail' = cSpuriousFail + 1` | None yet |
| 5.5 MemOrder | `cOrderGap < MaxOrderingGaps` | Model the implementation's actual ordering first. If the code really has a weak bridge, wrap that path, e.g. `MCStaleRead(t) == /\ cOrderGap < MaxOrderingGaps /\ StaleReadAllowedByImpl(t) /\ cOrderGap' = cOrderGap + 1`. **Best avoid hypothetical "what-if-we-relaxed-this-SC-label" wrappers** — a violation only re-confirms that some past commit's SC strengthening was necessary, which is information the closed PR already records; the MC run adds nothing beyond `git revert <commit> && cargo test`. Routing the wrapper into a separate "sensitivity config" does not change this; the work's value comes from the question being open, not from the cfg's label. See `code_analysis/references/concurrent-analysis.md` § 5.5 for the full prohibition. | `case-studies/dpdk-ring/spec/MC.tla` (`MCStall` / `MCStaleRead` / `MCRTSCaptureHead`); `case-studies/arc-swap/spec/MC.tla` (`MCWriterScanSlot` + `orderingGapCount`); `case-studies/left-right/spec/MC.tla` (`MCSkipReaderFence`, `MCSkipWriterFence`) |
| 5.6 ABA | no counter — modeled in base via slot/generation tags + reclamation pool | `Reclaim(addr) ==` returns addr to free pool; CAS tuple checks `(ptr, gen)` | `case-studies/dpdk-ring/spec/base.tla` (`NoABA` invariant); `case-studies/crossbeam-epoch/spec/base.tla` |
| 5.7 Caller misuse | `cIllegalCall < MaxIllegal` | external `ClientHarness` action set, one counter per misuse pattern | None yet — caller usually assumed cooperative |
| 5.8 Lost wakeup | `cSpuriousWake < MaxSpuriousWake` | `MCSpuriousWake(t) == /\ cSpuriousWake < MaxSpuriousWake /\ ParkedToReady(t) /\ cSpuriousWake' = cSpuriousWake + 1` without `notify` | `case-studies/libgomp/spec/MC.tla` (cancel-related wakeup paths) |

These wrapper shapes are schematic: adapt the counter names, record fields, and `UNCHANGED` clauses to your MC module. The important rule is that any fault wrapper with a budget must consume that budget on the transition; otherwise the "bounded" fault can fire forever.

For each row marked "None yet", that family is genuinely unmodeled in the existing case-study set. When generating a new spec where that family applies, you are writing the first reference example — keep the wrapper shape minimal and idiomatic so future case studies can reuse it.

### Counter Budget

Each new fault family adds a counter and a fresh non-deterministic action. State space typically grows multiplicatively.

Pre-flight check before adding the Nth counter:

- Estimate `states ≈ baseStates × ∏(boundᵢ + 1)`.
- If the projected count exceeds ~100M for the convergence config, set the new bound to 1 first and verify it still exposes the target interleaving.
- Hunting configs (`MC_hunt_<family>.cfg`) zero out unrelated counters — see the Hunting Configs section.

### Coverage Annotation

When you skip a family because the sub-category table says it does not apply, record the decision in the MC.tla header so coverage is auditable:

```tla
\* Fault model coverage:
\*   5.1 Interleaving:    via per-step actions (PushLoad / PushCheck / PushCAS)
\*   5.2 Cancellation:    n/a (synchronous API)
\*   5.3 OOM:             skipped (target documented to abort on alloc failure)
\*   5.5 MemOrder:        modeled via MCStaleRead / MCStall
\*   5.6 ABA:             modeled via slot+generation tag in base
\*   5.7 Caller misuse:   skipped (single-call API)
\*   5.8 Lost wakeup:     n/a (no wait/notify primitives)
```

If a target system has a domain-specific failure mode not in 5.1-5.8 (NIC reorder, signal-during-RMW, etc.), model it directly and add a row in the coverage block. The eight families are reference starting points, not a definition of "fault model".

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
