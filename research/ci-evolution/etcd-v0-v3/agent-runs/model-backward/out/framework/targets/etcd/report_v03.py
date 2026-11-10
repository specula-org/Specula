"""Render the evidence report from measured results, not expected transitions."""
import collections,json,pathlib,re

def render(d,R):
 run=R/d['run_root'];code=d['coverage']['code'];model=d['coverage']['model'];total=code['total']+model['total']
 baseline=d['comparisons']['baseline-code']['counts'].get('behavioral_mismatch',0)+d['comparisons']['baseline-model']['counts'].get('behavioral_mismatch',0)
 duration=sum(c['duration_seconds'] for c in d['commands']);maxcmd=max(c['duration_seconds'] for c in d['commands'])
 status=collections.Counter(code['statuses'])+collections.Counter(model['statuses'])
 oldstatus=collections.Counter()
 for part in ['old-code','old-model']:
  for line in (run/part/'implementation.jsonl').read_text().splitlines():oldstatus[json.loads(line)['observation']['status']]+=1
 action_table='| Action | Source descriptors | TLC-generated inputs |\n|---|---:|---:|\n'+'\n'.join(f"| `{k}` | {code['by_action'].get(k,0)} | {model['by_action'].get(k,0)} |" for k in code['by_action'])
 matrix='| Source / model | Route | Cases | Match | Behavior mismatch | Adapter error |\n|---|---|---:|---:|---:|---:|\n'
 for label,c in d['comparisons'].items():
  matrix+=f"| {label.rsplit('-',1)[0]} | {label.rsplit('-',1)[1]} | {c['total']} | {c['counts'].get('match',0)} | {c['counts'].get('behavioral_mismatch',0)} | {c['counts'].get('adapter_error',0)} |\n"
 timing='| Run | Seconds |\n|---|---:|\n'+'\n'.join(f"| {c['label']} | {c['duration_seconds']:.3f} |" for c in d['commands'])
 depths=[]
 for log in run.glob('*/model/*/tlc.log'):
  depths += [int(x) for x in re.findall(r'depth of the complete state graph search is (\d+)',log.read_text())]
 text=f'''# V03 Raft behavior evolution and local action validation

The evolved suite is in `out/repaired-spec`. All **{total} final direction instances match**: {code['total']} source-derived cases and {model['total']} TLC-generated cases. The inherited model disagreed on **{baseline}** of those instances. Matches include actual drops, panics and disabled caller operations; they are not all successful Raft transitions.

The supplied `old/source` is V02; `new/source` is V03. Initial `new/spec` copied the inherited model and was treated as a baseline, not as V03 fidelity. The final six-way replay is [`{d['run_root']}`]({d['run_root'].replace('out/','',1)}). [Machine-readable results](results.json), [all actual semantic deltas](evidence/semantic-deltas.json), [full disagreement evidence](evidence/disagreements.json), and the [run index](evidence/run-index.json) preserve inputs, actual pre/input/post, original failures and repaired reruns.

This establishes bounded local agreement only. No global protocol conformance, distributed reachability, intended-property change or real-bug discovery is claimed from injected state.

## Exact executed coverage

{matrix}

`baseline` means V03 Go versus inherited `new/spec`; `repaired` means V03 Go versus evolved suite; `old` means V02 Go versus actual `old/spec`. The old-model mismatches are retained evidence of pre-existing modeling errors. No V02 input was unsupported: the same mapped pre/input was executed on both supplied sources. Actual old drops/panics/disabled operations are reported as outcomes, not incompatibility.

All **239 prior source cases**, **103 prior TLC inputs** (identical pre/input/action), and the **21 prior version-control cases** are retained. The final source set adds {code['total']-239} cases. Sixty-three finite symbolic seeds generate {model['total']} cases through TLC and original model transitions. The two routes share descriptor vocabulary; they are complementary checks, not statistically independent evidence.

{action_table}

There are **{code['node_cases']+model['node_cases']} actual Node direction instances** ({code['node_cases']} source, {model['node_cases']} model): actual `node.run`, Ready/Advance channels, Status execution barriers, and callbacks followed by public Propose. Each matrix column executes its own source instance. Constructor, Bootstrap/Init, restart, live snapshots, empty log, zero Next, pause/inflight boundaries, pending equality, quota 0/15/16/17, mixed batches, snapshot applied cursors and post-Ready proposal rejection are covered.

Final V03 statuses: **{status['ok']} ok, {status['dropped']} dropped, {status['panic']} panic, {status['disabled']} disabled**. V02 statuses across the same direction instances: **{oldstatus['ok']} ok, {oldstatus['dropped']} dropped, {oldstatus['panic']} panic, {oldstatus['disabled']} disabled**. Exact IDs are in results.json.

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

V02 controls witness all four. Across baseline disagreements, {d['disagreement_classes']['V03 behavior change']} are source-version changes, {d['disagreement_classes']['V03 change plus pre-existing model repair']} combine a source change with a prior model repair, and {d['disagreement_classes']['pre-existing model repair']} are repair-only direction instances. These counts classify observations, not distinct bugs.

## Old/new semantic deltas

There are **{d['semantic_delta_counts']['behavior_changed']} changed** and **{d['semantic_delta_counts']['unchanged']} unchanged** source observations across comparable inputs. There are zero unsupported-old inputs or preparation/pre-input differences in that comparison. Rewriting a conf entry to normal is distinguished from an actual `ErrProposalDropped`; neither is labeled unsupported.

{(R/'out/evidence/semantic-delta-table.md').read_text()}

## Preserved implementation behavior and property assets

The model deliberately preserves empty explicit/implicit V2 admission in joint state followed by application panic; removed/demoted leaders retaining Leader role and early-return transfer state; positive configuration payload quota rejection; pending mutation despite a rejected append; the unchanged Hup scan omitting V2; outgoing-only live snapshot rejection; Next=0/empty-refill behavior and its injected empty-snapshot panic; and panic-before-transfer-cancellation partial effects. Some are implementation defects or suspicious boundary behavior, but the injected cases do not establish that they occur in a reachable distributed execution.

No correctness predicate was edited to pass. The full actual original suite is in [`assets/v02`](repaired-spec/assets/v02); [operator inventory](evidence/operator-inventory.json) and [integrity checks](evidence/input-integrity.json) verify preservation. Old invariant/property lists remain intact, including in Trace configurations. Representation additions and input-audit Next=0 support are separate from normative definitions.

`autoLeaveChecks.eligible` keeps its exact old meaning. Additional `crossingEligible`, old applied/pending/cursor, quota and `appended` evidence coexists with it. ProposalObservation adds the prior full configuration while ProposalContract stays unchanged. The inherited decision marker remains available and is no longer mistaken for a different call's return. [Property-phase handoff](repaired-spec/property-phase-handoff.md) explains these distinctions. No intended property edit is inferred solely from an implementation outcome.

## Mapping triage and disabled actions

The generic runner, protocol and eight comparator tests are byte-for-byte unchanged. **Zero actual pre/input mapping disagreements** remain or were observed in successfully executed pairs. One real output mapping omission was repaired separately: the TLA adapter had emitted ok for `DropNoLeader`; it now maps the actual proposal-drop outcome. That was not a Raft behavior repair.

The inherited V01-shaped old-source adapter failed compilation against V02; the failed log is retained. Bootstrap instance level binding, declaration order/projection editing, callback action framing and Update quantifier syntax initially failed as well. They are adapter/preflight failures, never disabled transitions or successful model output. [Triage](evidence/triage.json) links every error and repaired run. Failed outputs were not reused; each invocation used a fresh directory.

The seven final disabled instances are retained in the match totals: absent Node Ready delivery/Advance prerequisite, or a proposal channel disabled after a completed self-removal callback. A bounded actual channel wait follows a Status barrier. A callback's changed post-state is preserved even when its following proposal is disabled. The inherited V2 callback mismatch (model dropped a proposal that Go could not admit) was repaired rather than hidden. No other completed model relation lacks an observable successor in the tested domain.

Adapter changes are confined to source-version binding, nil-data encoding, actual Bootstrap/constructor/snapshot setup, explicit Ready persistence installation, added real API/channel calls and original-operator wrappers, status projection, finite descriptors and evidence export. No Python transition oracle or toy TLA replacement exists. Production Go remains unchanged apart from the package-local test adapter; all {d['input_integrity']['checked']} tracked source/spec/patch/framework inputs checked against the packet manifest are intact.

## Validation, durations and limits

{timing}

The final six-way matrix took **{duration:.3f} seconds**; the longest runner invocation took **{maxcmd:.3f} seconds**. Per-engine commands and durations, including all prior failed/diagnostic runs, are recorded in results.json and run-index.json. Eight unchanged comparator tests and the {total}-input structural audit passed. SANY preflight of **base, MC, Update and Trace** passed; LocalActions/ModelDomains were parsed/evaluated by every successful TLC invocation. Initial SANY errors are retained because SANY's process exit alone did not signal its semantic error. Final checks inspect the semantic diagnostics too.

Go uses GOMAXPROCS=2 and a 90-second outer timeout; offline modules and all working/temp/cache/output files remain in /workspace. TLC uses one worker, 2 GB heap, and 80 seconds per local process. Runner invocations are bounded at 180 seconds and the final matrix is serial. Maximum final local action-graph depth was {max(depths) if depths else 'unavailable'}. No safety or liveness invariant campaign ran: the adapter's Emit check only serializes finite candidates/results.

Limits: four server IDs and fixed option bounds; injected states rather than reaching cluster traces; message ordering abstracted as a multiset; measured limited protobuf/context domain; no arbitrary corrupt tracker/byte input campaign, unbounded log/pagination study, disk failures, broad concurrent Node schedules, crash/network search, random-timeout distribution validation, post-restart application replay or linear NDJSON Trace replay. Constructor/Bootstrap boundaries are real calls, but do not certify every lifecycle schedule. The zero-Next/partial-panic examples specifically carry no reachability claim.

Reproduce with `python3 out/framework/targets/etcd/build_v03.py`, then `python3 out/framework/targets/etcd/replay.py` (fresh output), then `python3 out/framework/targets/etcd/summarize.py --run-root <printed-root>`.
'''
 (R/'out/report.md').write_text(text)
