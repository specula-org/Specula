# Update-local correctness candidates

Derived independently from `old/source`, `new/source`, `update.patch`, and `state-vocabulary.md`. No prior invariant suite, maintenance conclusion, external source, or other agent was used. No tests or TLC were run; source was not modified.

[candidates.json](/workspace/out/candidates.json) contains **15 core candidates** and **3 unresolved questions**, including precise scoped predicates, concrete forbidden transitions, allowed controls, evidence locations, and required observations. Statements about either implementation are static hypotheses pending validation.

Notation: `I/O` = incoming/outgoing voters; `A` = acknowledged applied cursor; `P` = pending configuration index; `Q/M` = charged payload/limit. Actual `ApplyConfChange` is separate from `Advance`.

| ID | Obligation | Forbidden example → allowed nearby control |
|---|---|---|
| C01 | Admit configuration changes according to semantic enter/leave phase. | Empty **Explicit** change accepted inside joint, or refused outside joint → treat it as entering; a context-only change is leaving. |
| C02 | Serialize configuration appends and reserve automatic exits; one retained exit per actual joint episode. | Exit 5 appended with P=4, or exit 6 generated before deferred application of exit 5 → P covers 5 and actual exit application closes the episode. Conservative inherited-tail barriers remain allowed. |
| C03 | Automatic exit remains an obligation across leadership and application schedules. | Restored AutoLeave state with A=P=4 stays joint forever after leader entry 5 → eventually propose the exit under fair processing, without new client work. Explicit joint state may wait for a manual request. |
| C04 | Activate the requested configuration only on application. | Drop outgoing voters when exit is appended/committed → retain both halves until exit application, then activate staged learners. |
| C05 | Acknowledge only the captured Ready and retain newly generated work. | Advance of Ready ending at 4 consumes fresh exit 5/probes, or advances A to a later HardState.Commit → publish fresh effects in a later Ready and use the captured committed-page cursor. |
| C06 | Zero payload bypasses quota; ordinary positive payload retains backpressure. | Q=16,M=8 rejects an empty entry → accept it without charging bytes; reject another positive payload. The first oversized batch at Q=0 is allowed. |
| C07 | Release exactly the acknowledged committed payload, with saturation. | Subtract all persisted bytes instead of the committed page → Q=12 minus page cost 4 becomes 8; inherited cost exceeding Q saturates at zero. |
| C08 | Probe new peers without inventing replication knowledge. | Adding a peer sets Match to the leader tail → Match=0 with speculative Next is allowed, including dormant Next=0 for empty bootstrap. Preserve existing peers' evidence. |
| C09 | Start new-peer catch-up without waiting for another proposal or heartbeat. | Adding an empty peer emits nothing because committed is unchanged → emit a valid probe, then handle rejection/snapshot catch-up. Temporary snapshot unavailability permits deferral. |
| C10 | Use installed voter quorums and communicate newly enabled commits. | Removed leader counts itself, or exit commits using only the old half → use current voters/both joint halves. Previously committed entries remain committed after enlargement. |
| C11 | Cancel transfers when the target truly stops being a voter. | Final learner retains transfer target because Progress exists → clear it. A staged learner still in outgoing voters may remain the target. |
| C12 | Tail-snapshot acknowledgement immediately restores replication mode. | AppResp(11) leaves peer probing until new work → Replicate, Match=11, Next=12, and commit notification. Transport success alone may still wait for AppResp. |
| C13 | Use observer-local configuration during promotion lag. | Lagging learner refuses a valid vote solely as learner → grant it; candidate counts it if locally a voter. Mere Progress membership does not authorize solicitation/counting or learner campaigning. |
| C14 | Removed leaders reject new work and must not obstruct replacement forever. | Removed leader accepts new proposals or indefinitely suppresses elections with heartbeats → drop new work, finish retained work under the new quorum, and relinquish. Transient removed leadership is allowed. |
| C15 | Simple-change validation errors remain errors without partial installation. | Invalid change reports successful zero state or mutates original tracker → return error and preserve input. A valid first bootstrap voter remains allowed. |

Evidence anchors, with fuller old/new references in JSON:

- C01–C04: [configuration API](/workspace/new/source/raftpb/raft.proto:79), [semantic helpers](/workspace/new/source/raftpb/confchange.go:71), [RawNode transition tests](/workspace/new/source/rawnode_test.go:108), [explicit-transition trace](/workspace/new/source/testdata/confchange_v2_add_single_explicit.txt:100).
- C02–C07: [Advance changes](/workspace/new/source/raft.go:556), [deferred application contract](/workspace/new/source/node.go:159), [automatic-transition trace](/workspace/new/source/testdata/confchange_v2_add_double_auto.txt:34), [quota test](/workspace/new/source/raft_test.go:179).
- C08–C11, C15: [Progress initialization](/workspace/new/source/confchange/confchange.go:249), [configuration-switch intent](/workspace/new/source/raft.go:1556), [demotion transfer test](/workspace/new/source/raft_test.go:3617), [Simple contract](/workspace/new/source/confchange/confchange.go:125).
- C12–C14: [snapshot regression](/workspace/new/source/testdata/snapshot_succeed_via_app_resp.txt:102), [learner-vote regression](/workspace/new/source/testdata/campaign_learner_must_vote.txt:1), [removed-leader defect commentary](/workspace/new/source/testdata/confchange_v1_remove_leader.txt:189).

The cursor-crossing guard is an implementation mechanism, not the whole AutoLeave promise. C02/C03 therefore observe episode and exit history independently of P and A, including both deferred entering and deferred leaving application. Their liveness clauses require fair service and, for commitment, available joint quorums.

C09's immediate snapshot-only boundary is derived from catch-up intent and lacks a direct fixture; reachability needs validation. C14's eventual retirement is supported by explicit defect commentary, not by a passing liveness assertion. Neither is silently dropped because the implementation may violate it.

Unresolved; **not core requirements**:

- **U01 — positive-size configuration quota exemption:** the new comment says “Configuration changes are never refused,” but code and tests establish only the zero-payload exception. JSON records the stronger predicate and contrasting examples.
- **U02 — rollback after quota refusal:** both versions reserve P before append can fail. Exact rollback is plausible, but P is explicitly conservative; eventual AutoLeave progress is covered separately.
- **U03 — immediate removal handover:** eventual non-obstruction has intent support; synchronous step-down, a higher term, and choosing the greatest-Match successor are not established API guarantees.

Required extra observations are source-backed: configuration application/episode history, entry and Ready identities, append origin, inherited leadership barrier, transfer target, PendingSnapshot, and storage availability. No message-delivery ordering, global Next>Match, absolute Q<=M, or generic Raft safety inventory is imposed.
