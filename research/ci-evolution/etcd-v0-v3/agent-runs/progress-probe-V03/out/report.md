# C03 validation

**Verdict: rejected as a progress property satisfied by V03.** The intended automatic-exit requirement is supported by the API and tests. Under explicit healthy-service assumptions, TLC found a leadership-transfer liveness violation in V03 and a deferred-installation violation in both V03 and V02. The same-domain V02 leadership control completed successfully. These are **source-aligned model findings, not reproduced implementation bugs**.

Both primary V03 counterexamples start at the original model Init, execute every input in a complete 153-event setup prefix, and then follow a branching service driver calling the original reference actions. Both have fair repeating service cycles. Each was additionally replayed, including an extra copy of the cycle, with the original actions and **without VIEW**. No original source or behavior model was edited; no modeling repair was needed. All input-manifest hashes still match (`final-input-integrity.json`).

Machine-readable verdict, every TLC run, counts, commands, paths and limitations: [results.json](results.json). Detailed driver/refinement audit: [driver-audit.md](driver-audit.md). Concrete next-stage plan: [reproduction-plan.md](reproduction-plan.md).

## Intended requirement and scope

The relevant supplied V03 source sites are:

| Source | What it establishes |
|---|---|
| `versions/V03/source/raftpb/raft.proto:85–96` | Implicit joint transition automatically proposes a zero configuration change; explicit joint transition waits for the application. |
| `raftpb/raft.proto:111–113` | AutoLeave promises automatic transition to the final configuration when safe. |
| `node.go:153–175` | Ready batches must be applied in order; Advance may precede completion of application; ApplyConfChange remains a separate required callback. |
| `raft.go:556–583` | V03 releases quota, advances A, and auto-appends only if AutoLeave, leader, and `oldApplied < pendingConfIndex <= newApplied`. The automatic entry has nil Data. |
| `raft.go:747–755` | A new leader sets pendingConfIndex to its inherited last log index before appending the new leader normal entry. |
| `node.go:113–124` | Ready.appliedCursor uses committed entries or snapshot, not HardState.Commit; message-only Ready has cursor zero. |
| `rawnode_test.go:320–368` | The normal implicit path produces a leave; explicit mode requires a manual context-bearing leave. The last part of this test uses a stated application shortcut, so it is not proof of arbitrary distributed schedules. |
| `testdata/confchange_v2_add_double_auto.txt:34–62,121–138` | Processing the entering change produces a leave in the next Ready, and joint-quorum replication/application completes the exit. |
| `raft.go:1610–1627`, `raft_test.go:179` | Payload-based quota admission and the zero-payload rule; an oversized first proposal is allowed. |

Candidate paths beginning `new/source/` are interpreted as the supplied `versions/V03/source/` tree. V02's `raft.go:556–583` instead makes a level-triggered attempt on a positive applied cursor at/above pendingConfIndex; its marshaled leave has nonzero payload. These differences matter to the controls.

The comments support a conditional eventual response, not a universal wall-clock or fixed-step deadline. The normal same-call append is separately testable, but its strict cursor crossing must not become the liveness premise. The tested episode is the **applied** joint entry at index 5, not a synthetic restored snapshot. Snapshot-restored episodes remain an unexercised extension of C03 in this packet.

## Formal obligation

The executable definitions are in [C03Progress.tla](drivers/C03Progress.tla), with all-voter clock/service fairness in [C03Clocked.tla](drivers/C03Clocked.tla).

The setup identifies one episode `e`: request 1's entering entry `j=5`, incoming voters `I={1,2,4}`, outgoing voters `O={1,2,3}`. Its installation is detected from actual `cfgHist` and installed configuration, not from Commit or A. The monitor `barrier[n]` records the inherited `Last` immediately before an action makes n leader. It is a history fact, never an alias of pendingConfIndex. For the existing leader entering this episode, `max(j,barrier[n])=j`; for the new leader the inherited barrier is 5.

Define:

```text
Installed(n) = episode e actually installed, outgoing nonempty, AutoLeave=true
Exit(n)      = semantic empty Auto ConfChangeV2 after j retained in n's log
Eligible(n)  = Installed(n) and n is a leader in I union O
               and A[n] >= max(j, barrier[n])
               and not Exit(n)
               and no retained configuration entry has index > A[n]
Healthy      = every server alive, nonfatal, with storage available
Stable(n)    = eventually always (Healthy and n a leader in its voter union)
Settled      = the semantic exit actually applied on each of {1,2,4},
               each installed outgoing set empty and AutoLeave=false

ProposalProgress   = for every n: Stable(n) => (Eligible(n) ~> Exit(n))
CompletionProgress = for every n: Stable(n) => (Installed(n) ~> Settled)
```

`~>` is TLA+ leads-to. The specification includes weak fairness of prefix replay, the cyclic service pump, and pending follower ticks. The environment below supplies reliable delivery and joint quorums. No new client proposal is assumed after event 153.

A retained leave counts even if A already passed its index while application is deferred. Applied-exit detection uses the actual application history, not A. A historical `proposed` coverage bit is **not** the response predicate: in the leadership counterexample the old leader really proposed a leave, but it was overwritten, and the new stable leader has no retained exit. `proposed` only helps bound the optional transfer-injection window and record coverage.

`NormalCrossingEffect` is an additional normal-path assertion: a crossing-eligible Advance appends a semantic zero-payload leave. It passed together with progress in the normal control. It is not used as either liveness antecedent.

## Exact environment and domains

The complete settings, including every concrete domain value, are saved in [domains.json](domains.json), and each run directory contains its exact `.cfg` and `.tla` files.

| Setting | Focused domain/value |
|---|---|
| Server; bootstrap; joining | `{1,2,3,4}`; ordered `<<1,2,3>>`; `{4}` |
| RawNodes | All four for leadership/normal; `{}` for Node deferred-application scenarios |
| PreVoteNodes, CheckQuorumNodes, NoForwardNodes | All empty |
| RequestId | `1..32`; suffix invokes no client requests |
| PayloadWeights; EncodedWeights | `0..256`; `1..256` |
| ElectionTick; HeartbeatTick | 4; 1 |
| Initial timeouts | Auto prefix: node 1=4, 2=4, 3=5, 4=6. Explicit control prefix: 1=7, 2=5, 3=4, 4=6. All in legal `4..7`. |
| Later timeout arguments | Original trace arguments in prefix; current node timeout in suffix; all remain in `4..7` |
| MaxInflight; MaxMsgSize; MaxReadySize; MaxUncommitted | 2; 64; 64; 96 |
| Bootstrap payload/encoding; empty encoding | 6/14; 6 |
| Entering proposal payload/encoding | 24/32; Remove(3), AddVoter(4), transition Auto (JointExplicit in the manual control) |
| Automatic leave | V03 payload/encoding 0/6; V02 original payload/encoding 2/10 |
| SendPolicy; PersistPolicy; EarlyAdvance | Strict; Atomic; TRUE |
| ReadFence; CancelChanges; CancelUnknownRemovals; RecoveryMode | Inclusive; `{}`; TRUE; AppliedAdapter |

The suffix has no crashes, stop/restart, partitions, loss, duplication, storage unavailability, new client requests, compaction or snapshots. All original nodes receive fair caller/network service. Both joint majorities are available: at least 2 of `{1,2,3}` and at least 2 of `{1,2,4}`. Actual primary cycles have all four nodes live, caught up and applying in order.

The service ring is `Ready, StartPersist(All), CompletePersist(All), StorageApplySnapshot, StorageAppend, StorageSetHardState, Publish, QueueApplication, ApplyEntry, FinishApplication, Advance, Receive, ReturnAPI(1), Tick`, cycling node IDs 1,2,3,4 within each kind. It skips disabled slots, never replaces an action's effect. Publication and delivery choose one current message per relevant node with TLC CHOOSE. Thus these are serialized reliable-network scenarios, not all possible message orderings.

Heartbeat rounds begin only after preceding queues, Ready work and application jobs drain. The leader ticks, then every other current voter ticks once, then messages/work are serviced before the next round. This avoids infinite heartbeat injection and services a zero-output auto-append that needs a later heartbeat to send. The primary lassos each contain 16 Tick calls (four on each node), 24 receives, 24 publications, and 16 complete Ready/persistence/Advance service sequences per 192-action period.

Leadership injection is optional once, between any reference actions before the original leader's first automatic proposal. This remains a genuine branching suffix. Deferred installation is optional once, at any caller position/node with the entering entry queued. The chosen application can wait while publication/persistence completes, then the **original** Advance runs when legal, and application resumes in FIFO order. It does not force an impossible caller ordering or ban documented early Advance.

No focused term/log/state constraints, finite tick budget, response cutoff or fairness derived merely from budget exhaustion is used. Interaction budgets, service position, obligation monitors and real state are retained in fingerprints. The only VIEW mapping canonicalizes auxiliary readySeq, Ready.id and application-job.batch; its dependency audit and concrete replay validation are in `driver-audit.md`.

## Setup reachability and preflight

The source traces under `traces/V02` remain **V02 source execution evidence only**. The search reuses the exact input prefix through event 153: bootstrap/application, node 1 election in term 2, processing the ordinary leader entry 4, InvokeV2 at 152 and Propose at 153. It re-executes those inputs from the selected version's Init using `Trace.MatchEvent`; it does not use `TraceNext`'s old-post equality and does not import a source post-state as a seed.

`PrefixApplicable` rejects any disabled event. All final scenarios reached the complete prefix. The boundary is a real MODEL-reachable accepted, uncommitted joint proposal at index 5, with leader 1 applied/committed through 4. Both full recorded prefixes and compact input-only loaders are preserved. Node scenarios use fresh Init with the Node wrapper setting; they are not relabeled RawNode traces.

Preflight: Java 21.0.11, the supplied two-jar classpath, one TLC worker per run, 4 GiB heap for focused runs, 6 GiB for ordinary MC. Every TLC run has an outer timeout (15 seconds for the final SANY check, 45–600 seconds for TLC; none approaches the 30-minute cap). No `-coverage` telemetry was enabled. Every TLC command uses `-Dtlc2.TLC.progressInterval=10`. `preflight-final-sany.log` is clean. Early driver/configuration errors and their logs remain saved and are excluded from verdict evidence.

The initial ordinary run used unchanged MC.cfg. Its workload omitted V2, so it was a resource/safety baseline. A later ordinary run added V2 to the workload; otherwise its exact domains/bounds were unchanged: four model-value servers, three boot voters, RequestId `{1,2,3,4}`, payloads `{0,1,3}`, encodings `{1,2}`, election/heartbeat 3/1, inflight/message/Ready/quota caps 2, term/log/message bounds 5/14/20, and all original fault counters. Both entered Init/exploration but stayed shallow and timed out. Neither is a liveness verdict. This supports using reachable prefixes plus focused service exploration; it does not prove absence of other behaviors.

## Main results

The counts below are TLC generated/distinct state counts, not counts multiplied by the temporal tableau branches. Timeout rows use the last periodic count, so they are lower bounds on work performed. The complete inventory, including all diagnostic drafts, is in `results.json`; raw logs and per-run `run.json` retain exact runtimes and commands.

| Run | Outcome | Generated | Distinct | Wall time |
|---|---|---:|---:|---:|
| `ordinary-v03` | timeout_inconclusive | 166,279 | 162,247 | 60.35 s |
| `ordinary-v2-v03` | timeout_inconclusive | 138,096 | 137,232 | 45.36 s |
| `clocked-leadership-v03` | liveness_violation | 11,580 | 3,236 | 198.61 s |
| `clocked-leadership-v02` | completed_pass | 11,389 | 3,177 | 171.58 s |
| `clocked-deferred-v03` | liveness_violation | 4,634 | 1,331 | 72.49 s |
| `clocked-deferred-v02` | liveness_violation | 4,704 | 1,341 | 70.65 s |
| `entering-deferred-v02` | liveness_violation | 4,660 | 1,297 | 68.11 s |
| `normal-cost-control-v03` | completed_pass | 1,993 | 590 | 25.20 s |
| `explicit-control-v03` | completed_pass | 1,806 | 514 | 19.51 s |
| `witness-completion-v03` | nonvacuity_witness | 1,302 | 419 | 13.33 s |
| `clocked-witness-transfer-v02` | nonvacuity_witness | 2,825 | 891 | 10.90 s |
| `witness-explicit-v03` | nonvacuity_witness | 511 | 195 | 4.04 s |
| `concrete-replay-leadership-v03` | completed_pass | 2,888 | 852 | 6.51 s |
| `concrete-replay-deferred-v03` | completed_pass | 2,478 | 723 | 4.59 s |

The V02 leadership control uses the same server/request/payload/message domains, same prefix inputs, same all-voter clock driver, same transfer window, same properties and same VIEW as V03. The only differences are the supplied version's behavior and its source-backed automatic-leave encoding. The inverse eligibility probe fails as expected in V02, proving this pass did not come solely from an unreachable obligation. The normal successful-exit inverse probe and explicit-joint inverse probe likewise produce real TLC reachability counterexamples.

The original source's `TestRawNodeProposeAndConfChange` and `TestUncommittedEntryLimit` passed on both versions. V03's `TestInteraction/confchange_v2_add_double_auto` also passed. Commands/runtimes are in `source-controls.json`; tests ran offline with `GOTOOLCHAIN=local`, without source edits. These validate existing normal-path expectations, not the new failing schedules.

## Counterexample 1: leadership changes after the acknowledgement barrier

Primary artifacts: [TLC violation log](runs/clocked-leadership-v03/tlc.log), [original TLC JSON](runs/clocked-leadership-v03/counterexample.json), [event/state summary](runs/clocked-leadership-v03/events.json), [reference actions](runs/clocked-leadership-v03/reference-actions.json).

TLC reports `Error: Temporal properties were violated.` and a back edge from state 657 to state 466. There are 11,580 generated and 3,236 distinct states at detection. This is a fair lasso, not a timeout.

| Model state | Reference event and relevant effect |
|---:|---|
| 153 | Complete legal setup; term-2 leader 1 has joint proposal at 5, A=commit=4. |
| 175 | Receive on node 1 commits entry 5. |
| 179 | Nondeterministically placed `TransferLeader(1,2,timeout)` starts the handoff. |
| 194, 208 | ApplyEntry installs the joint AutoLeave episode on nodes 1 and 2. |
| 210 | Advance on leader 1 acknowledges 5 and correctly appends its term-2 leave at 6. |
| 211 | Follower 2 acknowledges 5; A2=5, and its log still ends at 5. |
| 234 | Queued TimeoutNow reaches node 2; it campaigns in term 3. |
| 291 | Voting makes node 2 leader: inherited barrier b2=P2=5, A2=5. It appends a normal term-3 leader entry at 6. It has no retained leave. |
| 300 | Replication overwrites node 1's **uncommitted** term-2 leave 6 with the new leader's normal entry. |
| 311 | New leader commits normal entry 6 with the available joint quorum. |
| 359 | Advance on leader 2 changes A2 from 5 to 6. The auto-leave guard tests `5 < 5`, so it appends no exit. |
| 466–657 | All nodes are alive, in term 3, applied/committed through 6. Node 2 stays leader, P2=5, outgoing `{1,2,3}`, AutoLeave=true, no retained exit. Healthy heartbeat/service rounds repeat. |

This meets Eligible without a crossing premise: installed episode, stable voting leader, A2≥max(j,b2), no retained exit and no unapplied configuration entry. Both proposal and completion remain false. Tracking application of the *entering* entry, or remembering that some earlier leader once proposed an exit, would miss it.

V02's same-domain search completes all 3,177 distinct states without a violation. Its level-triggered Advance can append an exit after acknowledging the new leader entry even when old A already equaled the inherited barrier. The eligibility probe gives a separate old-version witness. This is the regression-selective control.

## Counterexample 2: deferred ApplyConfChange installs AutoLeave too late

Primary artifacts: [TLC violation log](runs/clocked-deferred-v03/tlc.log), [original TLC JSON](runs/clocked-deferred-v03/counterexample.json), [event/state summary](runs/clocked-deferred-v03/events.json), [reference actions](runs/clocked-deferred-v03/reference-actions.json).

TLC reports a temporal violation and a back edge from state 528 to state 337. The completed explored graph contains 4,634 generated and 1,331 distinct states. All four servers use the Node wrapper setting.

| Model state | Reference event and relevant effect |
|---:|---|
| 175 | Leader 1 commits entering entry 5. Its installed configuration is still stable. |
| 192 | The caller nondeterministically chooses to defer application of the queued entering entry. Protocol state is unchanged by this scheduling decision. |
| 208 | After persistence, installation and publication requirements complete, original Advance acknowledges cursor 5. A1 becomes 5 while installed AutoLeave is still false. No leave is appended. Actual application history still ends at 4. |
| 220 | Original ApplyEntry executes ApplyConfChange and installs the joint AutoLeave configuration. A1=P1=5 already. |
| 337–528 | All nodes have actually applied 5, all queues/applications are serviced, leader 1 remains in term 2, A=P=commit=last=5, no exit retained. Four healthy heartbeat rounds form a repeatable cycle. |

The delayed callback completes; no subsequent committed batch is applied before it. Thus the counterexample does not depend on permanent application starvation or forbidden caller ordering. Message-only later Readys have appliedCursor=0, and no new client proposal is assumed.

V02 also has a fair deferred-installation violation under the identical all-voter clock (4,704 generated, 1,341 distinct states). The earlier leader-tick diagnostic also failed (4,660 generated, 1,297 distinct states). Its level trigger is inside the positive-cursor branch; after late installation no new positive-cursor Advance need occur. **Do not attribute this particular failure solely to V03.** The all-voter-tick runs and no-VIEW V03 replays confirm that the missing-heartbeat weakness of the supplied old pump is not the explanation.

## Retained-exit diagnostic, independent of the liveness verdict

Allowing the caller to defer any configuration entry found a separate `NoFatal` violation in both versions. In the V03 trace, node 1 defers application of leave 6 at state 375, acknowledges it while installed AutoLeave remains true, appends leave 7, then applies leave 6 and exits joint state. Applying leave 7 at state 469 produces `invalid configuration transition` in the reference. The analogous V02 trace is also saved.

Artifacts: `runs/fair-deferred-v03/counterexample.json` and `runs/fair-deferred-v02/counterexample.json`, with logs and summaries. This supports retaining the distinction between cursor acknowledgement, retained exit and actual callback completion. It is an additional model safety hypothesis, not an invented liveness failure or a reproduced Go panic. The primary progress search was then restricted to deferring the entering entry, leaving this finding intact.

## Full-reference admission and limits

All search transitions invoke original reference actions, with a scheduler-only stutter for choosing deferral. The VIEW erases only three auxiliary allocation identities after checking their uses across the supplied models. Every real state field, history record, budget and obligation monitor is retained. Concrete counterexample replay calls original actions from Init through the full prefix and two loop iterations, without VIEW; both replays pass action applicability, nonfatality, final still-joint/no-exit checks, and eventual script completion. The lasso can therefore be lifted to an infinite execution with increasing auxiliary IDs; it is not a convenient unreachable seed or fabricated back edge.

These tests reject satisfaction of C03's automatic-exit obligation on the supplied V03 model. They do not prove a universal property of V02, exhaustively search the full MC, test snapshot-restored seeds, or establish all message permutations. No reachable over-quota seed was constructed: normal same-call zero-cost behavior was checked, and the quota independence is also a direct source/model calculation because Weight(empty leave)=0 makes the positive-payload quota rejection condition false.

The independent actual-API reproduction stage must now confirm that the recorded input timing is executable and observe its concrete consequence. Follow [reproduction-plan.md](reproduction-plan.md), using the retained prefix and exact extracted reference actions, stopping on any inapplicable step. A model trace alone is not a reproduced implementation bug.
