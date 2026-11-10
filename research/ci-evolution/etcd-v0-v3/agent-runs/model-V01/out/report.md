Implemented a reusable JSON action-validation runner, generated Go/TLC adapters, finite target descriptors, and source-backed repairs in `out/repaired-spec`. This is a developmental pilot, not independent bug discovery or general conformance. No other agents, external sources, future versions, or prior experiment histories were used.

| Route | Cases | Baseline matches / mismatches | Repaired matches / mismatches |
|---|---:|---:|---:|
| Code → original model | 105 | 97 / 8 | 105 / 0 |
| TLC original transitions → Go | 43 | 33 / 10 | 43 / 0 |
| Total | 148 | 130 / 18 | 148 / 0 |

There are 122 distinct semantic inputs; 26 overlap deliberately across routes. All 148 pass the structural input audit and input/pre-state correspondence checks. Final adapter errors and unsupported cases: zero within the declared domains. The 18 baseline mismatches represent three behavioral model errors, not 18 independent bugs. The eight comparator fault-injection tests pass.

The source diff was reviewed against affected `base.tla` surfaces. Code-derived cases run real Go first, then TLC executes the supplied model operators. For the reverse route, TLC chooses finite combinations in the target domain, executes actual original operators/actions, and exports the selected pre-state/input and successor for Go replay. These are local action successors from injected states, not traces generated from the complete protocol Init. Shared descriptors/projections can create correlated errors; the provisional model was never treated as trusted.

The generic runner contains only process orchestration, JSON validation and comparison. The Go adapter calls real Raft methods; the TLA adapter invokes `Step`, `ApplyConfCore`, `Restore`, `RestartCore`, and the actual `ProtocolReady`/`ProtocolAdvance` transitions. No Python Raft oracle or substitute TLA protocol model exists. Baseline model files are copied verbatim per invocation; repairs are separate. Each result retains mapped actual input/pre-state, complete declared observation, raw execution evidence and field-level verdicts. Original invariants are neither edited nor tested as safety properties in this stage; TLC's `Emit` invariant is only a serialization hook.

| Action family | Code / TLC cases | Meaningful conditions |
|---|---:|---|
| Proposal | 9 / 6 | V1/V2 mixed batches; pending rewrite; quota rejection after bookkeeping; transfer/removed leader |
| Configuration application | 29 / 14 | Auto/implicit/explicit; empty/single/batch; joint leave; staged demotion; legacy demotion/promotion; zero/unknown target; last voter; self demotion; transfer cancellation; reduced-quorum commit and broadcast |
| Campaign | 10 / 4 | Unapplied V1/V2; pre-vote; singleton; outgoing-only self; learner |
| Read request | 8 / 2 | Simple/joint singleton distinction; current-term fence; both voter halves |
| Read acknowledgement | 2 / 1 | Joint partial/full quorum and queue release |
| CheckQuorum | 12 / 3 | Incoming-only activity, both halves, inactivity and activity reset |
| Ready | 12 / 2 | Raw read-only ownership vs Node acceptance; HS/SS, messages, reads, quota |
| Advance | 12 / 8 | Both caller modes; auto-leave on/off; cursor zero/positive; quota failure; follower; pending beyond cursor |
| Restore | 7 / 2 | Joint/staged metadata, outgoing-only recipient, learner, stale/fast-forward/non-follower |
| Restart | 4 / 1 | Real snapshot-backed constructor; simple/joint/outgoing/learner configurations |

The repairs affect only three behavioral definitions; see [repair.patch](evidence/repair.patch).

- `IsLeave`: an empty V2 batch leaves joint state only with transition `Auto`. Explicit/implicit empty batches request entry into joint state. Source: `raftpb/confchange.go:96–104`, `raft.go:1449–1454`. Eight baseline case instances distinguish this.
- `StepHup`: the unchanged `numOfPendingConf` recognizes only V1 entries. The provisional model blocked V2 campaigns that the source permits. Source: `raft.go:906`, `raft.go:1580–1588`. Four instances distinguish this. The repair preserves the implementation omission; it does not fix the code defect in the model.
- `AdvanceCore`: auto-leave requires a positive captured applied cursor. Without it, the baseline appended a leave or changed the retry index when Go did neither. Source: `raft.go:559–579`. Six instances distinguish this.

Snapshot restore/restart dropping outgoing voters, staged learners and AutoLeave is confirmed source behavior already represented by `RestoreProjection`; it is retained. No implementation correctness change was made. Original source/spec hashes are unchanged, with only `new/source/action_validation_test.go` added. The repaired copy differs only in the three documented spans; invariant bodies and every other copied file are unchanged.

Development adapter failures are retained separately under `out/evidence`: nil/non-nil entry size mapping, a stray normal-entry target, internal quota failure mislabeled as API drop, a TLC `EXCEPT` binding error, unavailable build temp paths, and initial input-domain flaws. These were corrected in adapters/descriptors, not counted as model repairs. Earlier runs with inadequate quota backing or decreasing log terms are diagnostic only. Final evidence is under `out/cases/baseline-*` and `out/cases/repaired-*`.

Final recorded subprocess time was approximately 10.14 seconds, excluding development and analysis. Every TLC invocation used one worker, a 2 GB heap, and a 175-second outer timeout; the longest final invocation was 1.32 seconds. Go used `GOMAXPROCS=2`, offline dependencies, and a 90-second outer timeout. Exact commands, durations, coverage, all mismatch fields, triage and repair details are in [results.json](results.json). Reproduction and adapter-regeneration instructions are in [framework/README.md](framework/README.md); [the observation descriptor](framework/targets/etcd/observations.md) specifies mappings, hidden state, exclusions and unsupported setup.

Follow-up invariant issues are recorded, not repaired: `CampaignDecisionEligibility` still treats V2 as campaign-blocking; `AutoLeaveAdvance`'s eligibility observer lacks the positive-cursor condition; `JointSnapshotRecovery` can expose the source's retained joint-state loss. These need a separate decision about intended correctness versus source alignment.

The next useful steps are to add actual Node channel/application schedules, obtain reachable cluster histories for the distinguishing local cases, and extend byte-preserving context and post-restart replay coverage. Current Node tests invoke the exact real ownership helpers but omit select/goroutine scheduling. Snapshots contain no application data; disk failures, bootstrap/status APIs, remote/lease reads and full crash/network schedules remain outside scope. The old snapshots were inspected but not executed; regenerate an old-version adapter to replay compatible saved cases. Resolve the recorded invariant questions before starting a bounded full-protocol campaign.
