# V02 action validation

The behaviorally repaired model matches **239/239 code-derived and 103/103 model-derived cases**. The provisional baseline has **18 mismatches** across the same 342 instances, with matching actual pre-states and inputs. There are no adapter errors in the final supported runs. The separate old-source subset matches 21/21; six intentionally invalid ConfStates remain outside conformance totals.

The generic JSON protocol, runner and eight comparator tests are byte-for-byte unchanged. No supplied invariant predicate was edited or checked. Go executes the supplied implementation; TLC executes original model operators/actions. There is no Python transition oracle, external browsing, other agent, later version or global protocol search.

| Family | Code cases | Baseline code mismatches | Model cases | Baseline model mismatches | Repaired matches code / model |
|---|---:|---:|---:|---:|---:|
| advance_node | 11 | 1 | 8 | 2 | 11 / 8 |
| advance_raw | 12 | 2 | 9 | 3 | 12 / 9 |
| apply | 29 | 4 | 14 | 4 | 29 / 14 |
| checkquorum | 12 | 0 | 3 | 0 | 12 / 3 |
| hup | 14 | 0 | 8 | 0 | 14 / 8 |
| proposal | 9 | 0 | 6 | 0 | 9 / 6 |
| read | 8 | 0 | 2 | 0 | 8 / 2 |
| readack | 2 | 0 | 1 | 0 | 2 / 1 |
| ready_node | 6 | 0 | 1 | 0 | 6 / 1 |
| ready_raw | 7 | 1 | 2 | 1 | 7 / 2 |
| receive | 10 | 0 | 3 | 0 | 10 / 3 |
| restart | 10 | 0 | 4 | 0 | 10 / 4 |
| restore | 13 | 0 | 6 | 0 | 13 / 6 |
| vote | 96 | 0 | 36 | 0 | 96 / 36 |
| **Total** | **239** | **8** | **103** | **10** | **239 / 103** |

Counts are direction instances, not independent discoveries. Code inputs retain all 105 prior cases and add 134 conditions; model seeds expand through original TLC domain selection to 103 instances, retaining the prior 43. All 342 pass structural audit. Logs, selected cases, input/pre-state comparisons and complete output differences are preserved in [the final suite](cases/v02-final-02) and [results.json](results.json).

**Concrete differences and repairs.** Only three behavior definitions change in [repaired-spec/base.tla](repaired-spec/base.tla); [the patch](adaptation/behavior-repairs.patch) is reviewable.

- **R1 — IsLeave:** four code and four model mismatches. Empty V2 explicit/implicit transitions enter joint state from a simple configuration in Go, while the baseline tries to leave and panics. From joint state Go panics on the attempted re-entry, while the baseline incorrectly leaves and promotes staged learners. Require `transition="Auto"` for leave. Evidence: `new/source/raftpb/confchange.go:101–105`, `raft.go:1478–1495`; this restores `old/spec/base.tla:522`. This includes both too restrictive and extra model behavior.
- **R2 — AdvanceCore:** two code and four model mismatches. With a zero captured applied cursor, the baseline appends automatic leave or advances the quota-retry pending index; Go does neither. Restore `b.cursor>0`, matching the enclosing branch at `new/source/raft.go:561`. The old repaired model already had this guard. This is extra model behavior.
- **R3 — ProtocolReady:** two code and two model mismatches. Public RawNode Ready and its empty Ready/Advance sequence execute successfully in Go, but the baseline relation is disabled by `ContainsUpdates`. Permit empty Ready for RawNodes; keep Node channel delivery gated by updates. Evidence: `new/source/rawnode.go:123–126`, `node.go:306–318`. TLC completed successfully and exported mapped disabled outcomes; these were not adapter errors. The empty Advance case identified a disabled Ready prerequisite explicitly.

The old StepHup repair is retained without another edit: `numOfPendingConf` still counts only legacy EntryConfChange at `new/source/raft.go:1605`. The model preserves this omission for V2. The live snapshot guard at `raft.go:1403–1406` still excludes outgoing-only recipients, including staged learners. Restore/restart now preserve full joint configuration metadata for accepted snapshots. These are source-backed local behaviors, not distributed bug claims derived from injected state.

**Adapters and domains.** ConfState names and old/new wrapper calls are bound explicitly. The updated projection adds actual vote-message fields, forced context, CheckQuorum and recorded votes. Advance setup calls original ProtocolReady and original Step actions, then compares the real captured input batch, action-entry state, live output and retained batch contents. Duplicate messages/read results are exercised. Node cases run actual `node.run` channels with Status barriers, including heartbeat, proposal, read acknowledgement and term changes between Ready and Advance. Restart pre-state is actual constructor storage/options, not an unrelated live raft object.

The 96 code-derived vote cases cover learner/voter/staged/removed recipients, regular/pre-votes, term/log freshness, repeated/conflicting votes, lease suppression/expiry and forced context. Candidate-response cases check that the receiver's own configuration controls counting, including both joint halves. Full recovery includes current learners, staged learners, AutoLeave, explicit joint mode, disjoint halves and outgoing-only/removed self. Existing proposal, config, read, quorum and auto-leave cases remain.

The old/new subset has 14 changed and 7 unchanged output projections. Learners now answer eligible votes; RawNode accepts output at Ready and preserves newly produced output across Advance; joint metadata survives recovery. Both versions separately match their models on all 21 selected cases. Advance pre-states can differ across versions because acceptance timing changed. [Full deltas](adaptation/version-deltas.json) retain these differences separately from within-version mapping checks. This subset tests the current diff; it does not redo the coordinator's V01 certification.

**Validity, disabled behavior and diagnostics.** The six malformed snapshots cover overlapping voters/learners, staged learners without joint state, and empty incoming voters. Go panics while the model admits configurations; mappings agree, but the structural audit rejects these inputs. They are classified as invalid setup, not repaired or counted as system defects. Generic comparison rows remain preserved as raw disagreements. Constructor panic state projections are diagnostic only.

Two adapter failures were corrected and retained: generated intermediate proposals at full quota initially raised setup errors on ErrProposalDropped; the adapter now continues the real schedule and keeps raw error evidence. A missing pair of parentheses in the new restart TLA mapping caused an evaluation failure; failed exported results were rejected. Every attempt used a fresh directory. The final suite has no missing/extra results, mapping disagreements or failed processes.

**Observer review is separate.** No observer correction is applied to the behavior-only tree. [The proposed patch](adaptation/observer-corrections.patch) adds the missing positive-cursor guard to `history.autoLeaveChecks.eligible`, supported by the zero-cursor cases and `raft.go:561`. `CampaignContract` still treats V2 as campaign-blocking; decide in the later invariant phase whether it intentionally exposes the source omission. `JointSnapshotMemberAcceptance` can expose outgoing-only rejection; obtain a reachable witness before interpreting it as a distributed failure. All safety/decision predicates and other model files are verified unchanged.

**Footprint and time.** 15 framework files were added/modified, all target bindings, domains, manifests, reporting or documentation; the three generic files have identical SHA-256 hashes. Per-file added/removed line counts and generated-data sizes are in results.json; [the complete adaptation patch](adaptation/framework-adaptation.patch) is retained. The behavior repair changes three expression lines plus one source comment. No supplied production source/spec/patch or prior input changed (223 immutable files checked).

First compatible current-version run: 261.7 seconds after starting. Executable adaptation finished after 714.9 seconds; total measured wall time through reporting: 1260.1 seconds. Final suite inner process time: 16.63 seconds; longest TLC invocation: 2.17 seconds. Each TLC process used one worker, a 2 GB heap and a 175-second outer timeout. Go used GOMAXPROCS=2, a 90-second outer timeout, offline modules and workspace-local cache/tmp. Commands and individual durations are in results.json and each invocation directory.

The eight unchanged comparator tests passed. Supplied learner/restore/Node/RawNode tests and complete confchange/quorum/tracker/raftpb package tests passed. The coordinator's integrity controls remain unchanged; no generic bug or need to rerun its old certification was found.

**Reproduce.** Run from `/workspace`:

```sh
python3 out/framework/targets/etcd/replay.py
```

[The portable suite manifest](framework/targets/etcd/suite.json) lists all six runs, relative paths, supplied tools, limits, all verification commands and regeneration commands. The replay script creates a unique exclusive root, leaving all previous evidence intact. After a rerun, use `python3 out/framework/targets/etcd/summarize.py --run-root <printed-root>` to regenerate the report. Bindings, saved inputs, symbolic domains, repaired model, schema and runner remain in the same framework organization for the next version.

**Remaining limits.** These are locally injected states with structural checks, not a proof of distributed reachability. Shared domains/projections permit correlated errors. Node channels are real but schedules are deterministic and do not cover cancellation, removal gating or arbitrary concurrency. The four-server action domain excludes the quorum allocation threshold; package tests are supplemental. Arbitrary bytes, snapshot data, remote/lease reads, disk failures, pagination boundaries, application replay and broad transport/crash schedules remain uncovered. Empty Node delivery and unknown-peer/local-message RawNode errors are unsupported domain dimensions. No safety claim or global search result is made. [The observation map](framework/targets/etcd/observations.md) records the full projection, ownership, error and uncertainty boundaries.
