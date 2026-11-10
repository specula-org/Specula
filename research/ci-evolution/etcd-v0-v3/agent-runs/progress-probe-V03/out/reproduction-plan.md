# Public-API reproduction stage

These are plans derived from MODEL executions. No failing application-level Go reproduction has been performed. Existing source tests passed; that does not establish these new schedules' implementation reachability or consequence.

Use the exact V02 and V03 source directories without editing `raft`, log cursors, pendingConfIndex, role, configuration, or progress. Prefer a deterministic single-threaded transport and explicit Ready/application queues. Retain the complete input prefix and logs listed below. Run both versions and record any first inapplicable action instead of replacing a state.

## Shared setup

Create servers 1, 2, 3 with peer order `[1,2,3]` and an empty joining server 4. Use ElectionTick=4, HeartbeatTick=1, MaxInflightMsgs=2, MaxSizePerMsg=64, MaxCommittedSizePerReady=64, MaxUncommittedEntriesSize=96, PreVote=false, CheckQuorum=false. The model settings use the trace's concrete protobuf sizes, not a new byte encoding. Propose the real `pb.ConfChangeV2{Transition: ConfChangeTransitionAuto, Changes: [RemoveNode(3), AddNode(4)]}`; do not emulate it by setting a ConfState.

The recorded prefix `joint-autoleave-prefix-full.ndjson` supplies all original V02 input messages/calls and source states through event 153. `joint-autoleave-prefix-inputs.ndjson` contains the same inputs. Replay inputs against fresh state in each version; source post-states from V02 are not V03 expectations. Campaign node 1 via the public API, drive/persist Ready until bootstrap entries 1–3 and leader entry 4 are acknowledged, then propose joint entry 5. Preserve the accepted-but-uncommitted boundary.

Map reference service actions to an adapter:

- `Ready`: retain the returned RawNode Ready, or receive one Node Ready from its channel.
- `StartPersist`/`CompletePersist`: perform and complete durable writes in the harness. `StorageApplySnapshot`, `StorageAppend`, `StorageSetHardState` expose that completed state through MemoryStorage, in the recorded legal order. Do not install nonexistent snapshots.
- `Publish`: enqueue the recorded Ready message only after required persistence. `Receive`: call `Step` with precisely that queued message. Do not inject a fabricated response.
- `QueueApplication`: enqueue the Ready's committed entries/snapshot on a FIFO application worker. `ApplyEntry`: decode real configuration entries and call `ApplyConfChange`, or apply the normal entry to the test state machine. Finish each batch before applying a subsequent one.
- `Advance`: `RawNode.Advance(savedReady)` or `Node.Advance()`, as appropriate. The latter is intentionally separate from the application worker.
- `Tick`: call the public Tick; generate heartbeats after draining the previous round. Tick every voter once per round.
- `TransferLeader`: `RawNode.TransferLeader(2)` on node 1, or `Node.TransferLeadership(ctx, 1, 2)` for a Node adaptation.

Use `RawNode.Status`/`BasicStatus` or `Node.Status`, returned `ConfState`, Ready entries, durable storage, and the application history as observations. Private A/P diagnostics can be added read-only during the reproduction stage but must not drive the application. Record term, leader, configuration, retained/committed entry types and indexes, every ApplyConfChange, all Advance cursors, and any panic.

## Primary leadership schedule (RawNode API)

Replay `runs/clocked-leadership-v03/reference-actions.json`; its TLA equivalent `drivers/ReplayLeadership.tla` already executes against the full reference without a VIEW, including two repetitions of the loop.

The important interleaving is:

1. Node 1 commits entry 5, with A1=4 and no installed joint configuration yet. Request transfer to node 2 (model state 179); let the original protocol determine when TimeoutNow and voting occur.
2. Apply joint entry 5 on nodes 1 and 2. Advance node 1: it appends a term-2 leave at index 6. That leave is not yet committed or retained by the transferee. Advance node 2 through entry 5.
3. Deliver the queued TimeoutNow to node 2 only after that acknowledgement. It campaigns and wins term 3 with its inherited tail ending at 5. Do not bypass votes or directly assign a leader.
4. The new leader appends its ordinary term-3 entry 6; replication overwrites node 1's uncommitted term-2 leave 6. Commit, apply, and Advance the new entry.
5. Continue ticks, persistence, message delivery, Ready service and ordered application with no new client proposals. In the model, V03's new leader has A2=6, P2=5, AutoLeave=true and no retained exit. The failed inequality is 5<5 when it acknowledges its fresh leader entry. The joint configuration persists through repeated healthy heartbeat rounds.

V02 control: use the same domains and transfer window, allowing messages emitted by that version to be serviced rather than demanding equality with V03 messages. Expect the level-triggered Advance to append a leave when the leader entry is acknowledged and for that leave to commit/apply. TLC completed all branches of this control, and the eligibility probe confirms the relevant new-leader obligation was reachable.

Do not treat a finite number of quiet heartbeats as a source-level proof of permanent nonprogress. Inspect the actual source trigger sites, verify no pending work/messages/applications remain that could change the diagnosis, and report the observed finite consequence separately.

## Deferred installation schedule (Node API)

Replay `runs/clocked-deferred-v03/reference-actions.json` conceptually through the real Node channels/application worker; use the concrete model run as the schedule guide, not as proof that Node select ordering will exactly match it.

1. Receive a Ready committing entry 5. Finish required persistence, storage installation, and all outgoing Ready messages.
2. Queue that batch for application, but delay the callback applying configuration entry 5. Call `Node.Advance()` first (model state 208).
3. Finish applying entry 5 with `Node.ApplyConfChange` before applying a later committed batch (state 220). This obeys the documented early-Advance exception and FIFO application rule.
4. Continue healthy ticks and service with no new proposals. The model has leader 1, term 2, A=P=commit=last=5, incoming `{1,2,4}`, outgoing `{1,2,3}`, AutoLeave=true, and no leave.

Run V02 too. This schedule also fails in its model: after late installation, heartbeat-only Ready batches have appliedCursor=0, so even the older level trigger receives no qualifying positive-cursor call. Do not describe this case as introduced solely by V03.

## Separate retained-exit diagnostic

`runs/fair-deferred-v03/counterexample.json` and the V02 counterpart defer the *leave's* ApplyConfChange. Acknowledge an existing leave, then finish applying it. The models can append another leave while the installed configuration is still joint, and subsequently reject applying the duplicate in a non-joint configuration. This is an additional hypothesis, not the liveness evidence above. Reproduce separately; do not conflate a model fatal with a real panic.
