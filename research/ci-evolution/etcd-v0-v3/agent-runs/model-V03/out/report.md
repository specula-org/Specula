# V03 Raft behavior evolution and local action validation

The evolved suite is in `out/repaired-spec`. All **653 final direction instances match**: 479 source-derived cases and 174 TLC-generated cases. The inherited model disagreed on **178** of those instances. Matches include actual drops, panics and disabled caller operations; they are not all successful Raft transitions.

The supplied `old/source` is V02; `new/source` is V03. Initial `new/spec` copied the inherited model and was treated as a baseline, not as V03 fidelity. The final six-way replay is [`out/cases/v03-final-03`](cases/v03-final-03). [Machine-readable results](results.json), [all actual semantic deltas](evidence/semantic-deltas.json), [full disagreement evidence](evidence/disagreements.json), and the [run index](evidence/run-index.json) preserve inputs, actual pre/input/post, original failures and repaired reruns.

This establishes bounded local agreement only. No global protocol conformance, distributed reachability, intended-property change or real-bug discovery is claimed from injected state.

## Exact executed coverage

| Source / model | Route | Cases | Match | Behavior mismatch | Adapter error |
|---|---|---:|---:|---:|---:|
| baseline | code | 479 | 355 | 124 | 0 |
| baseline | model | 174 | 120 | 54 | 0 |
| repaired | code | 479 | 479 | 0 | 0 |
| repaired | model | 174 | 174 | 0 | 0 |
| old | code | 479 | 473 | 6 | 0 |
| old | model | 174 | 168 | 6 | 0 |


`baseline` means V03 Go versus inherited `new/spec`; `repaired` means V03 Go versus evolved suite; `old` means V02 Go versus actual `old/spec`. The old-model mismatches are retained evidence of pre-existing modeling errors. No V02 input was unsupported: the same mapped pre/input was executed on both supplied sources. Actual old drops/panics/disabled operations are reported as outcomes, not incompatibility.

All **239 prior source cases**, **103 prior TLC inputs** (identical pre/input/action), and the **21 prior version-control cases** are retained. The final source set adds 240 cases. Sixty-three finite symbolic seeds generate 174 cases through TLC and original model transitions. The two routes share descriptor vocabulary; they are complementary checks, not statistically independent evidence.

| Action | Source descriptors | TLC-generated inputs |
|---|---:|---:|
| `proposal` | 97 | 27 |
| `apply` | 70 | 33 |
| `hup` | 14 | 8 |
| `read` | 8 | 2 |
| `checkquorum` | 12 | 3 |
| `readack` | 2 | 1 |
| `ready_raw` | 7 | 2 |
| `advance_raw` | 35 | 18 |
| `ready_node` | 7 | 2 |
| `advance_node` | 35 | 17 |
| `restore` | 14 | 6 |
| `restart` | 11 | 4 |
| `vote` | 96 | 36 |
| `receive` | 10 | 3 |
| `apply_then_step` | 30 | 4 |
| `bootstrap` | 3 | 1 |
| `bootstrap_hup` | 3 | 1 |
| `bootstrap_ready` | 3 | 0 |
| `construct` | 8 | 1 |
| `callback_node` | 8 | 3 |
| `propose_then_apply` | 6 | 2 |

There are **72 actual Node direction instances** (50 source, 22 model): actual `node.run`, Ready/Advance channels, Status execution barriers, and callbacks followed by public Propose. Each matrix column executes its own source instance. Constructor, Bootstrap/Init, restart, live snapshots, empty log, zero Next, pause/inflight boundaries, pending equality, quota 0/15/16/17, mixed batches, snapshot applied cursors and post-Ready proposal rejection are covered.

Final V03 statuses: **590 ok, 27 dropped, 29 panic, 7 disabled**. V02 statuses across the same direction instances: **571 ok, 47 dropped, 28 panic, 7 disabled**. Exact IDs are in results.json.

## Behavioral evolution

- Proposal admission follows pending-index precedence and the actual simple/joint phase checks, using `len(AsV2().Changes)==0`. It does not substitute the stricter `LeaveJoint()` test. Rejected configuration entries become nil normal entries before quota checks; pending bookkeeping occurs before a later append rejection.
- Advance releases committed payload quota first, applies its captured cursor, requires `oldApplied < pending <= newApplied` and a positive cursor, appends nil V2 for automatic leave, and records its appended index. Committed-entry and snapshot cursors and intervening core work are covered.
- Zero total payload bypasses a saturated/over-limit quota. Nonempty configuration data remains subject to quota despite the source's broad comment. Oversized first payloads remain accepted.
- New progress changes to Next=LastIndex; its existing active=true initialization is retained. Bootstrap therefore uses the bootstrap log length, and live restore self Match becomes snapshot index minus one. Constructor/restart still finish with Reset's Next=Last+1 and active=false; their final behavior is unchanged.
- Configuration application probes all progress, including existing peers and self, if commit did not advance. Actual pause, full inflights and empty/compacted refill behavior is retained. A commit advance still broadcasts.
- Transfer cancellation tests the incoming/outgoing voter union. Demotion cancels transfer once the target is no longer a voter; staged outgoing voters remain eligible. Existing early returns and panic ordering are preserved.

[Source mapping](repaired-spec/source-mapping-v03.md) binds base operators, MC/Update groups, Trace bindings and indirect callers. `Update` now includes legacy/normal proposal producers and progress/transfer consumers. Trace maps zero-payload auto-leave to the measured empty-entry encoding; its invariant list is unchanged. Campaign's sorted recipient order, formatter changes, equivalent log-unstable branches and temporary-variable/spelling changes have no additional observed effect at this multiset abstraction. The removed redundant `Simple` check was inspected; no new valid-domain behavior was inferred from it.

Four **pre-existing model repairs** are separate from V03's source changes:

1. Remove/re-add of a learner within one batch must delete and reinitialize Progress, not retain its old active/Next state.
2. Node callback proposal gating uses membership before/after application, including V2 leave after self-removal, rather than legacy `entry.target`.
3. A stale `decision=DropQuota` from a prior proposal is not a later append's return value. A per-call quota helper governs append behavior; the observation field is preserved. The first evolved model's false panics are saved in `repaired-post-drop-initial`.
4. A configuration-triggered broadcast panic stops before transfer cancellation. The model now preserves that partial state; the initial mismatch is saved in `repaired-panic-order-initial`.

V02 controls witness all four. Across baseline disagreements, 166 are source-version changes, 8 combine a source change with a prior model repair, and 4 are repair-only direction instances. These counts classify observations, not distinct bugs.

## Old/new semantic deltas

There are **174 changed** and **479 unchanged** source observations across comparable inputs. There are zero unsupported-old inputs or preparation/pre-input differences in that comparison. Rewriting a conf entry to normal is distinguished from an actual `ErrProposalDropped`; neither is labeled unsupported.

| Boundary / case | V02 Go / inherited model | V03 Go / evolved model |
|---|---|---|
| Phase: empty in simple (`v03-prop-simple-0-empty-auto`) | tail=V2; pending=3 (both) | tail=Normal; pending=0 (both) |
| Phase: nonempty in joint (`v03-prop-joint-0-v2`) | tail=V2; pending=3 (both) | tail=Normal; pending=0 (both) |
| Joint explicit empty, then apply (`v03-propose-apply-joint-JointExplicit`) | panic (both) | panic (both) |
| Zero payload over quota (`v03-quota-17-two-empty`) | dropped; last=3; quota=17 (both) | ok; last=5; quota=17 (both) |
| Nonempty V2 over quota (`v03-quota-17-v2-payload`) | dropped; pending=4 (both) | dropped; pending=4 (both) |
| Auto-leave crossing, quota 17 (`v03-advance-raw-cross-17`) | last=2; pending=2; quota=0 (both) | last=3; pending=3; quota=0 (both) |
| Auto-leave oldApplied=pending (`v03-advance-raw-equal-old-0`) | last=3; pending=1 (both) | last=2; pending=1 (both) |
| New peer (`v03-apply-new-voter-Leader`) | p4=next 3, probe False, active True; messages=0 (both) | p4=next 2, probe True, active True; messages=1 (both) |
| Probe existing self (`v03-probe-existing-self-probe`) | messages=0 (both) | messages=1 (both) |
| Demote transferee (`v03-apply-demote-Leader`) | transfer=3 (both) | transfer=0 (both) |
| Bootstrap 3 peers (`v03-bootstrap-123`) | self=match 0/next 4 (both) | self=match 0/next 3 (both) |
| Constructor resets progress (`v03-construct-joint-2`) | self=match 2/next 3 (both) | self=match 2/next 3 (both) |
| Live snapshot restore (`restore-simple`) | self=match 3/next 4 (both) | self=match 2/next 3 (both) |
| Learner remove/re-add (`v03-apply-remove-readd-learner-Follower`) | p4=next 3, probe False, active True / model: p4=next 3, probe False, active False | p4=next 2, probe False, active True (both) |
| Node V2 self-removal (`v03-callback-v2-leave-remove-self`) | disabled / model: dropped | disabled (both) |
| Empty-log add then propose (`v03-empty-log-Leader-apply_then_step`) | ok (both) | panic (both) |
| Advance after proposal drop (`v03-advance-after-drop-raw-14`) | pending=2; quota=2; ok / model: pending=3; quota=2; ok | pending=3; quota=0; ok (both) |
| Panic precedes cancellation (`v03-config-broadcast-panic-before-transfer`) | transfer=4; panic / model: transfer=0; panic | transfer=4; panic (both) |


## Preserved implementation behavior and property assets

The model deliberately preserves empty explicit/implicit V2 admission in joint state followed by application panic; removed/demoted leaders retaining Leader role and early-return transfer state; positive configuration payload quota rejection; pending mutation despite a rejected append; the unchanged Hup scan omitting V2; outgoing-only live snapshot rejection; Next=0/empty-refill behavior and its injected empty-snapshot panic; and panic-before-transfer-cancellation partial effects. Some are implementation defects or suspicious boundary behavior, but the injected cases do not establish that they occur in a reachable distributed execution.

No correctness predicate was edited to pass. The full actual original suite is in [`assets/v02`](repaired-spec/assets/v02); [operator inventory](evidence/operator-inventory.json) and [integrity checks](evidence/input-integrity.json) verify preservation. Old invariant/property lists remain intact, including in Trace configurations. Representation additions and input-audit Next=0 support are separate from normative definitions.

`autoLeaveChecks.eligible` keeps its exact old meaning. Additional `crossingEligible`, old applied/pending/cursor, quota and `appended` evidence coexists with it. ProposalObservation adds the prior full configuration while ProposalContract stays unchanged. The inherited decision marker remains available and is no longer mistaken for a different call's return. [Property-phase handoff](repaired-spec/property-phase-handoff.md) explains these distinctions. No intended property edit is inferred solely from an implementation outcome.

## Mapping triage and disabled actions

The generic runner, protocol and eight comparator tests are byte-for-byte unchanged. **Zero actual pre/input mapping disagreements** remain or were observed in successfully executed pairs. One real output mapping omission was repaired separately: the TLA adapter had emitted ok for `DropNoLeader`; it now maps the actual proposal-drop outcome. That was not a Raft behavior repair.

The inherited V01-shaped old-source adapter failed compilation against V02; the failed log is retained. Bootstrap instance level binding, declaration order/projection editing, callback action framing and Update quantifier syntax initially failed as well. They are adapter/preflight failures, never disabled transitions or successful model output. [Triage](evidence/triage.json) links every error and repaired run. Failed outputs were not reused; each invocation used a fresh directory.

The seven final disabled instances are retained in the match totals: absent Node Ready delivery/Advance prerequisite, or a proposal channel disabled after a completed self-removal callback. A bounded actual channel wait follows a Status barrier. A callback's changed post-state is preserved even when its following proposal is disabled. The inherited V2 callback mismatch (model dropped a proposal that Go could not admit) was repaired rather than hidden. No other completed model relation lacks an observable successor in the tested domain.

Adapter changes are confined to source-version binding, nil-data encoding, actual Bootstrap/constructor/snapshot setup, explicit Ready persistence installation, added real API/channel calls and original-operator wrappers, status projection, finite descriptors and evidence export. No Python transition oracle or toy TLA replacement exists. Production Go remains unchanged apart from the package-local test adapter; all 255 tracked source/spec/patch/framework inputs checked against the packet manifest are intact.

## Validation, durations and limits

| Run | Seconds |
|---|---:|
| baseline-code | 11.138 |
| baseline-model | 6.830 |
| repaired-code | 11.390 |
| repaired-model | 7.181 |
| old-code | 11.140 |
| old-model | 6.780 |

The final six-way matrix took **54.459 seconds**; the longest runner invocation took **11.390 seconds**. Per-engine commands and durations, including all prior failed/diagnostic runs, are recorded in results.json and run-index.json. Eight unchanged comparator tests and the 653-input structural audit passed. SANY preflight of **base, MC, Update and Trace** passed; LocalActions/ModelDomains were parsed/evaluated by every successful TLC invocation. Initial SANY errors are retained because SANY's process exit alone did not signal its semantic error. Final checks inspect the semantic diagnostics too.

Go uses GOMAXPROCS=2 and a 90-second outer timeout; offline modules and all working/temp/cache/output files remain in /workspace. TLC uses one worker, 2 GB heap, and 80 seconds per local process. Runner invocations are bounded at 180 seconds and the final matrix is serial. Maximum final local action-graph depth was 4. No safety or liveness invariant campaign ran: the adapter's Emit check only serializes finite candidates/results.

Limits: four server IDs and fixed option bounds; injected states rather than reaching cluster traces; message ordering abstracted as a multiset; measured limited protobuf/context domain; no arbitrary corrupt tracker/byte input campaign, unbounded log/pagination study, disk failures, broad concurrent Node schedules, crash/network search, random-timeout distribution validation, post-restart application replay or linear NDJSON Trace replay. Constructor/Bootstrap boundaries are real calls, but do not certify every lifecycle schedule. The zero-Next/partial-panic examples specifically carry no reachability claim.

Reproduce with `python3 out/framework/targets/etcd/build_v03.py`, then `python3 out/framework/targets/etcd/replay.py` (fresh output), then `python3 out/framework/targets/etcd/summarize.py --run-root <printed-root>`.
