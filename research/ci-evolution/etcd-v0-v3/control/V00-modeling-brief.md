# Modeling Brief: etcd-raft V00

## 1. System Overview

- **Target:** upstream `d58d5d159ae1a1f644a10003f2d8b3b807cd0b3a`; checkout `98047a97b87252c328c9c6eee3fe72671d23a785` adds only `go.mod`/`go.sum`. Production source is the intended V00.
- **Category A — Distributed / Message-Passing:** Go Raft library; serialized protocol steps interact with asynchronous messages, caller persistence/application, membership, and recovery (`node.go:313`, `rawnode.go:31`, `storage.go:40`). No BFT overlay.
- **Scale:** 18 library implementation Go files, 4,774 lines including comments; additionally `doc.go` (300), README (197), design (57), and message schema (95). Generated protobuf serialization is outside scope.
- **Architecture:** Node owns one event-loop goroutine; RawNode requires external serialization. Neither provides physical persistence or transport (`README.md:12`, `node.go:245`, `rawnode.go:31`). A core `Step` is distinct from Ready delivery, storage, sending, application, and Advance.
- **Revision-specific scope:** PreVote, CheckQuorum, transfer, progress/flow control, single-node applied configuration changes and learners, snapshots, recovery, and ReadOnlySafe. Joint-quorum arithmetic exists, but no production path populates the second voter half (`tracker/tracker.go:99`, `tracker/tracker.go:168`, `raftpb/raft.proto:78`). Do not invent joint transitions.
- **Evidence/status:** current source and supplied tests only. Historical commit mining, issues and PRs are excluded by run instructions: all archaeology counts are zero, not evidence of no historical bugs. Ordinary `go test -mod=readonly -p 8 -count=1 ./...` passed; no TLA+ model, traces, or formal checks were produced in this analysis phase. Detailed evidence and gaps: [analysis-report.md](analysis-report.md).

## 2. Scenarios

Historical evidence is intentionally unavailable for every Scenario. Priorities reflect source interactions, potential contract impact, and modeling suitability; no implementation bug is claimed confirmed.

### Scenario 1: Protocol promises cross Ready, durability, and recovery boundaries

**Mechanism:** Volatile protocol decisions, captured Ready batches, durable storage, and recovered state can advance independently.
**Evidence:** `raft.send` queues only (`raft.go:400`); Ready may overlap logically committed and unstable entries (`node.go:224`, `node.go:573`); Advance acknowledges captured endpoints (`node.go:390`, `node.go:409`, `rawnode.go:44`); RawNode infers newness from `LastIndex()==0` after loading saved state (`rawnode.go:77`, `rawnode.go:85`), unlike RestartNode (`node.go:253`).
**Affected code paths:** `newRaft`, `NewRawNode`, `RestartNode`, `newReady`, `commitReady`, `node.run`, `unstable.stableTo`, `loadState`, caller Storage adapter.
**Suggested modeling approach:** Variables `durableHS`, `durableLog`, `durableSnap`, `storageView`, `unstable`, `readyBatch`, `raftApplied`, `appApplied`, `incarnation`; actions extract/persist/publish/apply/Advance/crash/restart. Preserve exact entry `(index,term)` and snapshot-index acknowledgments. HardState is one logical record; do not invent torn term/vote writes. Split operations at caller completion boundaries, with storage-call interleavings where source reads can race compaction.
**Priority:** High. **Rationale:** Recovery and externally visible promises underpin all other scenarios. README's same-batch send allowance versus Ready field ordering, and snapshot/HardState recoverability, require explicitly labeled caller interpretations, not a hidden conservative loop (`README.md:114`, `node.go:58`). MC-4/5.

### Scenario 2: Election and transfer eligibility depend on local configuration progress

**Mechanism:** Ordinary campaigns, transfer campaigns, vote grants, and vote counting use different guards while configurations and roles can change between events.
**Evidence:** Hup scans committed entries above the Raft applied cursor (`raft.go:859`); TimeoutNow checks promotability without that scan (`raft.go:1264`); transfer votes bypass recent-leader suppression (`raft.go:766`, `raft.go:791`); learner grants are blocked but receiver/candidate membership is not otherwise checked (`raft.go:885`); PreVote continuation calls `campaign`, whose unpromotable check only logs (`raft.go:729`, `raft.go:1215`).
**Affected code paths:** `Step`, `campaign`, `stepCandidate`, `stepFollower`, `tickElection`, `tickHeartbeat`, `applyConfChange`, `TallyVotes`, wrapper response filtering.
**Suggested modeling approach:** Variables role/term/vote, per-node voters/learners, phase-specific votes, logical timers, leader/transfer target, configuration application cursor; actions retain real PreVote term exceptions and separate Hup/TimeoutNow/PreVote-continuation branches. Keep each core call atomic, with configuration callbacks and network delivery between calls.
**Priority:** High. **Rationale:** Election/history safety and management progress require composition of freshness, participation, persistence, and configuration lag; equal configuration at every node cannot be assumed. Transfer settles by success, timeout, or cancellation, not guaranteed target election. MC-6.

### Scenario 3: Released application work and effective membership are different state

**Mechanism:** Configuration admission/election guards use the Advance cursor, while effective membership changes through a separate application callback.
**Evidence:** Advance may precede application (`node.go:145`, `node.go:154`); `raftLog.applied` is an instruction cursor (`log.go:35`); pending-conf admission uses that cursor and can rewrite a proposal to an empty normal entry (`raft.go:977`); membership takes effect on application under the old configuration (`README.md:193`); promotion preserves progress, demotion is ignored, and removal can leave leader role intact (`raft.go:1403`).
**Affected code paths:** `Ready.appliedCursor`, both Advance paths, `stepLeader/MsgProp`, `applyConfChange`, `newRaft`, snapshot restore and configuration replay.
**Suggested modeling approach:** Retain proposed/logged/committed/released/config-applied positions, actual voter/learner sets per node, `pendingConfIndex`, and deterministic cancellation. Model early Advance and ordered delayed application. Preserve self-removal, duplicate additions, update-node no-op, and quota failure after pending-conf bookkeeping. Check transition safety independently of the source guard; do not assume its success proves serialized effective changes.
**Priority:** High. **Rationale:** This is the implementation's configuration protocol, not a peripheral extension. Restart must recover coherent configuration even when `Config.Applied` suppresses replay (`raft.go:325`, `raft.go:373`, `storage.go:95`). MC-1 and CR-2/4.

### Scenario 4: Replication evidence and snapshot boundaries change at different times

**Mechanism:** Match/Next, send quota, volatile/stable suffixes, snapshots, and application cursors describe different stages of catch-up.
**Evidence:** Three progress states and state-dependent rejection guards (`tracker/progress.go:79`, `tracker/progress.go:169`); heartbeat frees quota without advancing Match (`raft.go:1093`); snapshot status and installation responses take different paths (`raft.go:1058`, `raft.go:1122`); full restore moves firstIndex/commit without moving applied, whereas Hup's scan is unclamped (`log.go:299`, `log_unstable.go:35`, `raft.go:866`).
**Affected code paths:** `maybeSendAppend`, `handleAppendEntries`, `handleHeartbeat`, `MaybeUpdate/MaybeDecrTo`, `restore`, `MemoryStorage` snapshot/compaction methods, Hup, Ready/Advance.
**Suggested modeling approach:** Retain effective log plus durable suffix/compaction boundary, pending snapshot and symbolic history/configuration, progress mode/Match/Next/probe flag/quota endpoints/activity. Split snapshot create/send/receive/persist/apply/status/ack, retaining atomic full-restore core work. Encode actual fatal/error branches as observable outcomes, not disabled actions. Nonempty prefix batching and quota saturation/release remain explicit.
**Priority:** High. **Rationale:** Tests of each local helper do not settle composition with crash, compaction, timers, and delayed storage. Keep temporary snapshot unavailability and required transport failure reports. MC-3/7.

### Scenario 5: ReadIndex evidence must survive membership and application interleavings

**Mechanism:** Read initiation, leadership confirmation, captured commit index, queue-prefix release, delivery, and actual read response occur at different times and may observe different configurations.
**Evidence:** Non-singleton current-term gate and self-ack (`raft.go:995`); current voter set at heartbeat-ack evaluation (`raft.go:1109`); queue releases earlier contexts with a later confirmed request (`read_only.go:78`); singleton checks only cardinality (`tracker/tracker.go:119`); self-removal keeps role while proposal guard has no matching ReadIndex guard (`raft.go:966`, `raft.go:1464`).
**Affected code paths:** `ReadIndex`, read forwarding/response, `readOnly.addRequest/recvAck/advance`, `stepLeader`, `applyConfChange`, both Ready wrappers, caller read completion.
**Suggested modeling approach:** Variables read invocation/context/requester, captured index, initiating/confirming term and configuration observations, ack set, queue, delivered ReadState, actual applied history, and client response. Preserve singleton fast path as written and all term/reset behavior; check a valid read basis rather than imposing `leader => member`. Correlate each response to its request and application prefix.
**Priority:** High. **Rationale:** A ReadState and a nil ReadIndex return are not completed reads. Read-only safety requires evidence independent of the implementation branch selected; configuration changes may occur between registration and confirmation. MC-2; TV-1/3 address wrapper/context progress.

### Scenario 6: Admission, rejection, cancellation, and retry are protocol outcomes

**Mechanism:** API handoff and internal acceptance do not uniformly signal logging, consensus, configuration application, or completion.
**Evidence:** Node.Propose waits for a core result; ProposeConfChange acknowledges handoff (`node.go:442`, `node.go:455`, `node.go:473`); RawNode returns core errors directly (`rawnode.go:143`); no-leader Node proposals can wait on a disabled channel (`node.go:339`); quota/pending-conf logic and Ready-driven quota release differ from actual commit/application (`raft.go:977`, `raft.go:1530`, `node.go:407`).
**Affected code paths:** wrapper method handoff/result/stop, proposal forwarding and drop paths, pending-conf rewrite, size accounting, read-state clearing and transfer settlement.
**Suggested modeling approach:** Variables request ID, handoff/core decision/result, effective entry kind, payload weight, uncommitted quota, cancellation/stop status and retry lineage. Separate source outcomes from application-defined successful writes; cancellation after handoff permits uncertain effects. Preserve RawNode's whole-buffer read-state clear on Advance (`rawnode.go:67`) as a distinct wrapper behavior.
**Priority:** Medium. **Rationale:** Reusable outcome contracts prevent vacuous checks that inspect only unchanged state after a rejection. Small helper discrepancies belong in test/review verification; wrapper lifecycle state composes with every protocol scenario. TV-1/2/3 and CR-3/4.

## 3. Modeling Recommendations

### 3.1 Model (with rationale)

Build one connected Category A reference with scenario-focused checking configurations; no disconnected bug models. The matrix specifies planned coverage, not completed modeling. `Pending` means no generated model/harness, trace validation, negative-trace check, or bounded exploration yet; the ordinary suite pass is separate.

| Core mechanism → current source evidence | Modeled behavior and interactions | General properties (§5) | Planned public-interface harness family | Validation |
|---|---|---|---|---|
| Elections/PreVote/CheckQuorum → `raft.go:619,784,1188` | All roles/term exceptions, activity windows, configuration lag and durable votes; S1/2/3 | ElectionSafety, VoteRecovery, QuorumAccounting, ElectionProgress | H1 elections/options, partition/rejoin and restart | Pending |
| Leadership transfer → `raft.go:1086,1151,1264` | Catch-up, forced campaign, ignored/replaced target, timeout/removal; S2/4 | ElectionSafety, NoUnexpectedFatal, TransferSettlement | H2 transfer with ordinary lag and target changes | Pending |
| Append/commit → `raft.go:596,1291`; `log.go:88,291` | Log freshness/conflict, current-term commit, heartbeat cap, unstable self Match; S1/4 | LogMatching, LeaderCompleteness, CommittedHistory, PromiseBacking | H3 proposals, normal overwrite of uncommitted suffix and leader changes | Pending |
| Progress/retries/flow control → `tracker/progress.go:79,169`; `raft.go:445,1039` | Probe/Replicate/Snapshot, rejection hints, quota, nonempty/empty batch distinction; S4/6 | ReplicationEvidence, QuotaIntegrity, CatchupProgress | H4 bounded messages/Ready pages, lost/reordered/duplicate valid traffic | Pending |
| Membership/learners → `raft.go:977,1403`; `tracker/tracker.go:168` | Per-node applied configurations, promotion, no-op/cancel, removal, config lag; S2/3/5 | ConfigurationOrigin, ConfigurationTransitionSafety, LearnerEligibility, ManagementProgress | H5 committed add/promote/remove, deterministic cancellation, delayed callbacks | Pending |
| Snapshot/compaction → `raft.go:1327`; `storage.go:170,188,213` | Matching-log fast path/full restore, symbolic snapshot prefix/config, retained dummy term, status versus install; S1/3/4 | SnapshotBacking, AckPreservation, NoUnexpectedFatal, CatchupProgress | H6 legal create/compact/install, availability recovery and status ordering | Pending |
| Ready/Advance/persistence → `node.go:313,573`; `rawnode.go:44,185` | Captured batch versus live state, durable completion, early Advance, pagination and application; S1/3/6 | ReadyAccounting, PromiseBacking, AppliedAgreement, OutcomeSoundness | H7 both wrappers, independent storage/application rates and intervening inputs | Pending |
| Bootstrap/join/restart → `node.go:198,253`; `rawnode.go:72`; `raft.go:320` | Bootstrap entries, empty-peer joining, durable-only recovery, Config.Applied/config coherence; S1/2/3 | VoteRecovery, RecoveryBacking, ConfigurationOrigin | H8 clean start, joining, log/snapshot recovery; empty-log state remains an explicit question | Pending |
| ReadOnlySafe → `raft.go:995,1093,1274`; `read_only.go:56` | Request/forward/confirm/queue/deliver/application/return, singleton and changed configs; S3/5 | ReadBasis, ReadApplication, ReadCorrelation, ReadProgress | H9 leader/follower/learner reads, delayed application, leadership changes and retry | Pending |
| API outcome/quota/quiescence → `node.go:473`; `raft.go:1530`; `rawnode.go:124` | Admission/drop/rewrite/cancel/stop, size limits, ordered callbacks; quiesced ticks only with stated caller premise | OutcomeSoundness, QuotaIntegrity, ReadyAccounting | H10 normal rejection/retry/cancellation and quiesced-to-active handling | Pending |

Retain finite node identities, terms, indexed symbolic commands/configurations, message multiplicity and identities, and snapshot prefix witnesses. Abstract bytes into separate payload/encoded-size classes; keep quota thresholds, oversized-first-batch allowance, nonempty prefixes, batching and ordering (`util.go:101,129`). Abstract tick counts finitely while retaining randomized timeout alternatives, transfer deadline and CheckQuorum window. Full abstraction/caller tables are in analysis-report §§3,7; no bound is a proof for larger domains.

### 3.2 Do Not Model (with rationale)

Exclude KV/MVCC, transaction/gRPC APIs, physical WAL/OS behavior, serialization bytes, metrics and numeric performance, Byzantine/fabricated traffic, and clock-based lease reads per guidance. Exclude unreachable joint transitions/ConfChangeV2, live voter demotion, and any future implementation; retain current helper arithmetic/source behavior as correspondence evidence. Omit Go allocation/ring layout from protocol state; review helper contracts separately. CheckQuorum remains in scope despite lease-read exclusion. Do not suppress fatal branches, self-removal, rejections, pending snapshots, or recovery to obtain passing properties.

## 4. Proposed Extensions

| Extension | Variables | Purpose | Scenario |
|---|---|---|---|
| External effects and crash recovery | durableHS/log/snap, storageView, unstable, incarnation, readyBatch, raftApplied, appApplied | Preserve source/caller atomicity and recover durable obligations | 1/3/4 |
| Options and management state | preVote/checkQuorum, phase votes, elapsed counters, activity, transferee | Exact term exceptions and progress conditions | 2/3 |
| Applied single-change configuration | voters/learners, configApplied, pendingConfIndex, config-entry/cancel history | Cross-node lag, eligibility, predecessor quorum and recovery | 2/3/5 |
| Detailed catch-up | Match/Next/mode, ProbeSent, inflight endpoints, snapshot stage, firstIndex/boundaryTerm | Distinguish evidence from optimistic scheduling; retain retry/error outcomes | 4 |
| Read and request observations | request/context IDs, read queue/acks, captured index, readStates, response history, proposal decision/weight | Independent safety/progress and nonvacuous outcome checking | 5/6 |
| Explicit unexpected-error state | fatalReason, storage availability, failed operation observation | Keep code panics reachable; distinguish legal transient failure from environment fault | 1/2/4/6 |

## 5. Proposed Invariants

Safety targets are independent predicates over behavior/history, not premises of protocol actions. Core panic branches must be represented so NoUnexpectedFatal can fail. Record every volatile commit transition, but distinguish it from durable consensus or externally published commitment obligations: an unexposed, unpersisted singleton entry may disappear on crash. Published assertions enter obligation history whether or not their backing is valid; PromiseBacking checks that independently. Source evidence and precise history rules are in analysis-report §6.

| Invariant | Type | Description | Targets |
|---|---|---|---|
| ElectionSafety / LogMatching / LeaderCompleteness | Safety | One elected leader per term; equal indexed term implies equal prefix; later elected leaders contain prior commitment obligations or snapshot witness | All; S2/4 |
| CommittedHistory / AppliedAgreement | Safety | No live overwrite below the logical commit cursor; durable/published commitment obligations survive recovery; actually applied prefixes agree across replicas, including snapshot history | S1/3/4 |
| VoteRecovery / RecoveryBacking / PromiseBacking | Safety | Recovery preserves durable term/vote obligations; recovered commit has data backing; externally published promises and successful commands have required recoverable backing. No unconditional volatile commit ≤ local durable index | S1; MC-4/5 |
| ConfigurationOrigin / ConfigurationTransitionSafety | Safety | Effective configurations derive from bootstrap, committed deterministic callbacks or valid snapshots; successive effective changes preserve this revision's predecessor-quorum/serialization contract under allowed cursor lag | S2/3; MC-1/6 |
| LearnerEligibility / QuorumAccounting | Safety | No local learner campaign/grant or learner-counted majority; election/commit/read decisions count distinct relevant voters. Do not forbid all votes by removed nonlearners | S2/3/5 |
| ReplicationEvidence / SnapshotBacking / AckPreservation | Safety | Distinguish volatile self Match from remote response evidence and check required backing at publication/use; snapshots represent their prefix/configuration; old batch acknowledgments preserve newer unstable replacements | S1/4; MC-7 |
| ReadyAccounting / QuotaIntegrity / OutcomeSoundness | Safety | Correct captured batch endpoints, ordered delivery with no skips, faithful quota accounting, and justified admission/drop/rewrite/cancel/result decisions; API nil is not commit success | S1/3/6; TV-1/2 |
| ReadBasis / ReadApplication / ReadCorrelation | Safety | Returned read has a valid leadership/commit basis within its invocation-response interval, its required prefix actually applied, and matching request identity; singleton identity and queue-prefix confirmation require evidence | S3/5; MC-2 |
| NoUnexpectedFatal | Safety | Legal protocol/API scheduling and specified nonfatal storage conditions do not reach internal panic/bounds failures | S1/2/4/6; MC-3/6 |
| ElectionProgress / CatchupProgress | Liveness | With eventual usable storage/network, an eligible quorum/configuration, continued effective ticks and a period allowing an election to finish, a leader can emerge and an eligible lagging replica catch up | S1/2/4 |
| ManagementProgress / TransferSettlement | Liveness | With predecessor/successor quorums, ordered continuing application and fair service/retries, eligible changes can advance; a non-replaced transfer attempt succeeds or times out/cancels | S2/3/6 |
| ReadProgress | Liveness | With stable eligible leadership/configuration, current-term evidence where required, quorum communication, caller service, suitable contexts and sufficient actual application, retried reads can complete | S5/6 |

No universal proposal commitment, exactly-once execution, read completion during arbitrary partitions, or election convergence from fairness alone. Preserve invocation/response histories to check real-time ordering, not merely equal read indexes. The read comments say “greater than/further than” (`node.go:63,168`); justify inclusive-prefix mathematics explicitly rather than silently changing the textual fence. Caller assumptions/ambiguities, including same-batch send ordering, must accompany every checking result.

## 6. Findings Pending Verification

### 6.1 Model-Checkable

All entries are forward-looking questions with verified source premises, not confirmed bugs or operational reproduction instructions. No historical fix is a target. Use general properties in the coherent reference; no property-specific adversary that edits source behavior.

| ID | Description | Expected invariant violation if the concern is real | Scenario |
|---|---|---|---|
| MC-1 | Can permitted early Advance and delayed configuration callbacks admit/elect using configuration progress insufficient for successive changes? `node.go:154,410`; `raft.go:866,980` | ConfigurationTransitionSafety, ElectionSafety, CommittedHistory | 3/2 |
| MC-2 | Do membership changes, retained leader role and count-only singleton/read-queue paths always preserve the basis of completed reads? `raft.go:995,1109,1464`; `tracker/tracker.go:119` | ReadBasis, ReadApplication | 5/3 |
| MC-3 | Can election work and pending full snapshot restore interact with the unclamped unapplied-entry scan under legal Ready scheduling? `raft.go:866,1377`; `log.go:299`; `node.go:384` | NoUnexpectedFatal, CatchupProgress | 4/2 |
| MC-4 | Across documented Ready persistence/publication orders and crash boundaries, are promises and recovered commit always backed? Interpret conflicting caller text explicitly. `README.md:116,118`; `node.go:58,595`; `raft.go:1497` | PromiseBacking, RecoveryBacking | 1 |
| MC-5 | Can a legally initialized empty-log RawNode with saved obligations encounter the constructor's new-node inference on recovery? `rawnode.go:77,85`; `raft.go:565` | VoteRecovery, NoUnexpectedFatal; downstream election safety remains unestablished | 1 |
| MC-6 | Do promotion/removal and delayed configuration application across Hup, transfer, and PreVote continuation preserve eligibility/history and progress? `raft.go:729,859,1215,1264,1403` | ElectionSafety, NoUnexpectedFatal, ManagementProgress | 2/3 |
| MC-7 | Do rejection/backtracking, heartbeat quota release, snapshot notifications and compaction always preserve matching evidence and eventual catch-up? `tracker/progress.go:169`; `raft.go:1039,1093,1122` | ReplicationEvidence, SnapshotBacking, CatchupProgress | 4 |

### 6.2 Test-Verifiable

| ID | Description | Suggested verification |
|---|---|---|
| TV-1 | RawNode clears all current readStates when advancing an older batch containing reads; Node clears at emission (`rawnode.go:67,185`; `node.go:406`) | Review batch ownership and permitted sequential inputs; ordinary lifecycle testing only if within run boundaries; no claimed lost-result reproduction |
| TV-2 | pendingConfIndex is set before quota admission can fail (`raft.go:977,990,1530`) | Review rejected-request bookkeeping and subsequent permitted retry outcomes; preserve no-op transformation and proposal-loss contract |
| TV-3 | Empty read context can enter pending map while empty heartbeat context is ignored (`read_only.go:56`; `raft.go:1105`) | Clarify valid-context contract; functional coverage of context correlation/progress, no stale-read claim |

### 6.3 Code-Review-Only

| ID | Description | Suggested action |
|---|---|---|
| CR-1 | Ready Entries/message, snapshot durability, SnapshotFinish and read-fence text differ in precision or from code (`README.md:116,118`; `node.go:69,180`; `raft.go:1130`) | Record explicit caller interpretations and unresolved correspondence; source behavior remains authoritative for transitions |
| CR-2 | Config.Applied may suppress configuration replay while MemoryStorage supplies snapshot ConfState (`raft.go:325,373`; `storage.go:95`) | Establish recoverable applied-state/configuration coherence from the chosen caller adapter; do not invent replay |
| CR-3 | FreeFirstOne advertises empty no-op but reads the buffer before count check (`tracker/inflights.go:108`); sole Raft caller checks Full with positive capacity | Helper-contract audit; no current protocol impact established; do not discard from later review |
| CR-4 | RemoveNode unconditionally invokes tracked-peer-only RemoveAny (`raft.go:1445`; `tracker/tracker.go:142`) | Resolve absent/repeated removal legality and deterministic cancellation contract; no assumed idempotency or confirmed defect |

## 7. Reference Pointers

- [analysis-report.md](analysis-report.md): complete audit, source/atomicity maps, excluded suspicions, caller assumptions, abstraction limits, property definitions, harness/observability plan, and phase status; [code-analysis-tests.log](code-analysis-tests.log): this run's ordinary test output.
- Source anchors are relative to `../source/`: `raft.go:320-1576`, `node.go:49-604`, `rawnode.go:31-282`, `log.go:24-372`, `log_unstable.go:19-159`, `storage.go:40-271`, `tracker/`, `quorum/`, `read_only.go:19-121`, `raftpb/raft.proto:12-95`.
- Reference algorithm is Raft; supplied `README.md:191-197`, `doc.go:172-195`, and `design.md:1-57` document implementation deviations. Paper links in source were not fetched; no external algorithm implementation or prior model was used.
- Follow the existing next-phase Specula workflow. Model/harness generation, positive and controlled-invalid trace validation, nonvacuity checks and completed bounded checking remain required initialization work. Do not advance CI `current`, alter verdicts, delete properties, or modify production behavior to obtain a baseline.
