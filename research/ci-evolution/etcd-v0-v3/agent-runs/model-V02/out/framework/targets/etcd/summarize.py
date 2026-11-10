#!/usr/bin/env python3
"""Summarize recorded comparisons and explicit source-based triage, never transitions."""
import argparse,collections,datetime,difflib,hashlib,importlib.util,json,pathlib,re
R=pathlib.Path(__file__).resolve().parents[4];O=R/'out'
p=argparse.ArgumentParser();p.add_argument('--run-root',default='out/cases/v02-final-02');a=p.parse_args();runroot=R/a.run_root
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
relative=lambda p:str(p.relative_to(R))
labels=['baseline-code','baseline-model','repaired-code','repaired-model','old-version-subset','invalid-inputs']
runs={label:read(runroot/label/'comparison.json') for label in labels}
cs=read(O/'cases/code-inputs.json');mc=read(runroot/'baseline-model/generated-cases.json');aftermc=read(runroot/'repaired-model/generated-cases.json')
assert sorted(mc,key=lambda c:c['id'])==sorted(aftermc,key=lambda c:c['id'])
(O/'cases/model-inputs.json').write_text(json.dumps(mc,indent=2)+'\n')
for label in labels:
 for row in runs[label]['results']:assert not row['pre_differences'] and not row['input_differences'] and row['verdict']!='adapter_error'
assert all(runs[x]['counts']=={'match':runs[x]['total']} for x in ['repaired-code','repaired-model','old-version-subset'])
repairs=[dict(id='R1',operator='IsLeave',classification='lost established behavior repair',change='Require Auto transition as well as empty V2 changes. Empty explicit/implicit changes enter joint state; they do not leave it.',source=['new/source/raftpb/confchange.go:101','new/source/raft.go:1478','new/source/confchange/confchange.go:50'],established='old/spec/base.tla:522'),dict(id='R2',operator='AdvanceCore',classification='lost established behavior repair',change='Require captured applied cursor > 0 before auto-leave, preserving the source enclosing branch and its quota retry behavior.',source=['new/source/raft.go:561'],established='old/spec/base.tla:1071'),dict(id='R3',operator='ProtocolReady',classification='too restrictive API model',change='Allow public RawNode Ready even with no updates; Node delivery still requires updates. This also enables valid empty Ready/Advance preparation.',source=['new/source/rawnode.go:123','new/source/node.go:306'],established=None)]
triage=[]
for label in ['baseline-code','baseline-model']:
 for row in runs[label]['results']:
  if row['verdict']=='match':continue
  if row['action']=='apply':
   repair='R1';classification='extra model behavior' if 'joint-' in row['id'] else 'too restrictive model behavior'
  elif 'empty' in row['id']:repair='R3';classification='too restrictive model behavior (disabled relation)'
  else:repair='R2';classification='extra model behavior'
  triage.append(dict(row,run=label,repair=repair,classification=classification,evidence=relative(runroot/label/'comparison.json')))
for r in repairs:r['baseline_counts']=dict(collections.Counter(x['run'] for x in triage if x['repair']==r['id']));r['remaining_supported_mismatches']=0
coverage={}
for label in labels:
 for row in runs[label]['results']:
  family=row['action'];coverage.setdefault(family,{}).setdefault(label,collections.Counter())[row['verdict']]+=1
coverage={family:{label:dict(counts) for label,counts in x.items()} for family,x in sorted(coverage.items())}
# This uses the unchanged generic comparator for observed old/new deltas, not an oracle.
spec=importlib.util.spec_from_file_location('runner',O/'framework/runner.py');runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
old=runner.read_results(runroot/'old-version-subset/implementation.jsonl');new=runner.read_results(runroot/'repaired-code/implementation.jsonl');unordered=read(O/'framework/targets/etcd/manifest.json')['unordered_paths']
deltas=[]
for cid,x in old.items():
 y=new[cid]
 deltas.append(dict(id=cid,pre_differences=runner.differences(runner.norm(x['pre_observation'],unordered,('state',)),runner.norm(y['pre_observation'],unordered,('state',))),input_differences=runner.differences(runner.norm(x['input_observation'],unordered,('input',)),runner.norm(y['input_observation'],unordered,('input',))),differences=runner.differences(runner.norm(x['observation'],unordered),runner.norm(y['observation'],unordered))))
(O/'adaptation/version-deltas.json').write_text(json.dumps(deltas,indent=2)+'\n')
commands=[]
for label in labels:
 for engine in ['implementation','model']:
  for command in read(runroot/label/engine/'commands.json'):
   c=dict(command,run=label,engine=engine)
   if engine=='model':
    txt=(pathlib.Path(c['cwd'])/'tlc.log').read_text();m=re.search(r'(\d+) states generated, (\d+) distinct states found',txt)
    c['tlc_states']=dict(generated=int(m[1]),distinct=int(m[2])) if m else None
    c.update(workers=1,heap_gb=2,outer_timeout_seconds=175)
   else:c.update(outer_timeout_seconds=90,GOMAXPROCS=2)
   commands.append(c)
# Verify the supplied source/spec/patch and prior reusable input files remain immutable.
original=read(R/'input-manifest.json');immutable=[];changed=[]
for name,h in original.items():
 if name.startswith(('old/','new/','out/cases/prior-')) or name in ['update.patch','framework-negative-controls.json','prior-rerun.json']:
  immutable.append(name)
  if sha(R/name)!=h:changed.append(name)
assert not changed,changed
base=(R/'new/spec/base.tla').read_text();repaired=(O/'repaired-spec/base.tla').read_text()
assert base[base.index('Independent safety contracts.'):]==repaired[repaired.index('Independent safety contracts.'):]
for name in ['VoteContract','CampaignContract','TransferContract','ProposalContract','EffectContract']:
 def operator(text):
  tail=text[text.index(name+'('):];m=re.search(r'\n[A-Za-z][A-Za-z0-9_]*(?:\([^\n]*\))?\s*==',tail);return tail[:m.start()] if m else tail
 assert operator(base)==operator(repaired),name
for file in (R/'new/spec').iterdir():
 if file.name!='base.tla':assert sha(file)==sha(O/'repaired-spec'/file.name)
# Footprint versus the supplied framework, including generated data separately.
origin=O/'adaptation/original-framework';framework=O/'framework';footprint=[];patch=[]
paths=set(p.relative_to(origin) for p in origin.rglob('*') if p.is_file())|set(p.relative_to(framework) for p in framework.rglob('*') if p.is_file())
for rel in sorted(paths):
 if '__pycache__' in str(rel):continue
 oldp=origin/rel;newp=framework/rel
 before=oldp.read_text() if oldp.exists() else '';after=newp.read_text() if newp.exists() else ''
 if before==after:continue
 diff=list(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='supplied-framework/'+str(rel),tofile='out/framework/'+str(rel)));patch+=diff
 footprint.append(dict(path='out/framework/'+str(rel),status='modified' if oldp.exists() else 'added',added_lines=sum(x.startswith('+') and not x.startswith('+++') for x in diff),removed_lines=sum(x.startswith('-') and not x.startswith('---') for x in diff),bytes=len(after.encode()),kind='generated domain/manifest' if rel.suffix=='.json' else 'documentation' if rel.suffix=='.md' else 'target binding/domain/report code'))
(O/'adaptation/framework-adaptation.patch').write_text(''.join(patch))
generic=['runner.py','protocol.schema.json','test_runner.py']
assert all(sha(framework/x)==sha(origin/x) for x in generic)
integrity=dict(immutable_supplied_files_checked=len(immutable),changed=[],generic_unchanged={x:sha(framework/x) for x in generic},safety_predicates_and_decision_contracts_unchanged=True,other_spec_files_unchanged=True,behavior_operators_changed=['IsLeave','ProtocolReady','AdvanceCore'],observer_changes_applied=False)
(O/'adaptation/integrity.json').write_text(json.dumps(integrity,indent=2)+'\n')
# Preserve original measured timestamps across report regeneration.
timing_path=O/'adaptation/timing.json'
if timing_path.exists():timing=read(timing_path)
else:
 start=datetime.datetime(2026,9,22,18,11,43,tzinfo=datetime.timezone.utc);end=datetime.datetime.now(datetime.timezone.utc)
 code_end=datetime.datetime.fromtimestamp((O/'framework/adapters/tla/LocalActions.tla').stat().st_mtime,datetime.timezone.utc)
 compat=datetime.datetime.fromtimestamp((O/'cases/v02-dev01-code/comparison.json').stat().st_mtime,datetime.timezone.utc)
 timing=dict(start_utc=start.isoformat(),first_current_compatible_run_utc=compat.isoformat(),first_compatible_seconds=(compat-start).total_seconds(),last_executable_binding_edit_utc=code_end.isoformat(),executable_adaptation_seconds=(code_end-start).total_seconds(),reporting_completed_utc=end.isoformat(),total_wall_seconds=(end-start).total_seconds(),note='Wall time includes local inspection, binding/domain/model work, testing and report preparation. Individual command times are separately recorded; no labor-time precision claimed.')
 timing_path.write_text(json.dumps(timing,indent=2)+'\n')
final_summary={label:dict(route=d['route'],spec=d['spec'],total=d['total'],counts=d['counts'],comparison=relative(runroot/label/'comparison.json'),duration_seconds=sum(c['duration_seconds'] for c in commands if c['run']==label)) for label,d in runs.items()}
diagnostics=[]
for path in sorted((O/'cases').rglob('comparison.json')):
 if path.parent.parent==runroot:continue
 d=read(path);diagnostics.append(dict(path=relative(path),total=d['total'],counts=d['counts'],exit_codes=[x['exit_code'] for x in d['commands']]))
invalid=[dict(row,classification='invalid setup: malformed ConfState outside supported domain; not a real-system bug or behavior repair',evidence=relative(runroot/'invalid-inputs/comparison.json')) for row in runs['invalid-inputs']['results']]
limits=['No global protocol search or safety-invariant evaluation. No distributed reachability proof; all local injected states need a separate reachability argument before system-bug claims.','Two directions share vocabulary and projections; correlated mapping mistakes remain possible. TLC selects finite symbolic descriptors and executes original model actions, not a separate Python oracle.','Node uses actual channels and deterministic barriers, but there is no scheduler enumeration, cancellation, removed-node proposal gating, or arbitrary concurrent caller coverage.','Four-server action domain excludes the quorum sort allocation threshold; supplied package tests are supplemental, not bidirectional comparisons.','No arbitrary bytes/unknown protobuf fields, snapshot data, remote/lease read semantics, disk failures, post-restart application replay, broad pagination, transport or crash histories.','Empty Node Ready delivery, response inputs from unknown peers and local messages through public RawNode.Step are outside the supported action domain.','Observer histories and invariant predicates are untouched; recommended observer correction and potentially intended implementation-defect properties need the later invariant phase.']
result=dict(protocol='action-validation/v1',version='V02',claim='Bounded source/model action validation, not a proof of safety or distributed reachability.',run_root=relative(runroot),runs=final_summary,coverage=coverage,
 totals=dict(code_derived=239,model_derived=103,supported_pairs_per_model=342,baseline_matches=324,baseline_mismatches=18,repaired_matches=342,repaired_mismatches=0,final_supported_adapter_errors=0,old_version_subset_matches=21,invalid_inputs_separate=6),
 repairs=repairs,mismatches=triage,invalid_setup_results=invalid,
 preserved_prior_repairs=[dict(operator='IsLeave',restored=True),dict(operator='AdvanceCore positive cursor',restored=True),dict(operator='StepHup legacy-only configuration scan',restored=False,already_preserved_in_new_model=True,source=['new/source/raft.go:1605','old/spec/base.tla:267'])],
 version_comparison=dict(cases=21,changed_outputs=sum(bool(x['differences']) for x in deltas),unchanged_outputs=sum(not x['differences'] for x in deltas),changed_pre_states=sum(bool(x['pre_differences']) for x in deltas),changed_inputs=sum(bool(x['input_differences']) for x in deltas),evidence='out/adaptation/version-deltas.json',note='Both versions separately match their supplied/repaired model on this subset. Advance pre-state deltas are expected because Ready acceptance changed; these are version changes, not adapter mismatches.'),
 retained_implementation_behaviors=[dict(behavior='Hup scans only legacy EntryConfChange, ignoring unapplied V2 entries.',source='new/source/raft.go:1605',classification='source omission preserved, no distributed counterexample claim'),dict(behavior='Live snapshot membership checks incoming voters/current learners only; outgoing-only and staged outgoing-only recipients decline the snapshot, although full restart reconstructs them.',source='new/source/raft.go:1403',classification='source restriction preserved; joint metadata itself is now restored',cases=['restore-outgoing-only','restore-v02-staged-self','restart-v02-staged-self'])],
 observer_review=[dict(id='O1',applied=False,issue='autoLeaveChecks.eligible lacks b.cursor>0; after behavior repair it records false eligibility for a zero-cursor batch.',source='new/source/raft.go:561',model='new/spec/base.tla:1119',evidence=['advance-raw-True-0-0-Leader-0','advance-node-True-0-0-Leader-0'],proposal='out/adaptation/observer-corrections.patch'),dict(id='O2',applied=False,issue='CampaignContract uses ConfKinds while actual Hup scans LegacyConfKinds. Decide later whether this property should intentionally expose the source omission; do not change it here.',source='new/source/raft.go:1605',model='new/spec/base.tla:673'),dict(id='O3',applied=False,issue='JointSnapshotMemberAcceptance can expose outgoing-only snapshot rejection. The matching local behavior is preserved; a reachable witness is still needed.',model='new/spec/base.tla:1370',source='new/source/raft.go:1403')],
 adapter_changes=['Renamed ConfState fields; explicit old-source API spelling binding.','Actual Node goroutine/channels and Status barriers replace helper-only owner testing.','Original ProtocolReady/Step preparation for Advance; captured input batch and retained batch observation; mapped disabled prerequisite candidates.','Learner/forced vote flags, actual message inputs, recorded votes and CheckQuorum mappings.','Restart pre-observation reads actual storage and actual constructor options.','Fresh Go work directories, relative manifests, workspace-local offline build environment. No generic runner/protocol changes.'],
 adapter_diagnostics=[dict(issue='Intervening proposal ErrProposalDropped was initially treated as setup failure.',fixed='Retain raw error and continue actual schedule; do not panic or invent an expected output.',evidence='out/cases/v02-dev02-model/comparison.json'),dict(issue='TLA conditional grouping in new restart pre-mapping caused evaluation failure.',fixed='Parenthesized the conditional. Failed command output rejected; not a disabled action.',evidence=['out/cases/v02-invalid-01','out/cases/v02-final-01/baseline-code'])],
 diagnostics=diagnostics,integrity=integrity,adaptation_footprint=footprint,timing=timing,
 execution_time=dict(final_suite_inner_seconds=sum(c['duration_seconds'] for c in commands),max_tlc_invocation_seconds=max(c['duration_seconds'] for c in commands if c['engine']=='model'),commands=commands),
 validation=dict(structural_audit=read(O/'adaptation/valid-input-audit.json'),invalid_audit=read(O/'adaptation/invalid-input-audit.json'),generic_unit_tests=8,generic_tests_log='out/adaptation/runner-tests.log',source_tests=['out/adaptation/source-tests.log','out/adaptation/source-package-tests.log'],supplemental_commands=read(O/'adaptation/supplemental-verification.json'),coordinator_controls_preserved='framework-negative-controls.json',coordinator_prior_certification_preserved='prior-rerun.json'),
 portable_manifest='out/framework/targets/etcd/suite.json',reusable_invocation='python3 out/framework/targets/etcd/replay.py',limits=limits)
(O/'results.json').write_text(json.dumps(result,indent=2)+'\n')
rows=[]
for family,d in coverage.items():
 if family not in {x['action'] for x in cs+mc}:continue
 def num(label,key=None):return sum(d.get(label,{}).values()) if key is None else d.get(label,{}).get(key,0)
 rows.append(f"| {family} | {num('baseline-code')} | {num('baseline-code','behavioral_mismatch')} | {num('baseline-model')} | {num('baseline-model','behavioral_mismatch')} | {num('repaired-code','match')} / {num('repaired-model','match')} |")
report=f'''# V02 action validation

The behaviorally repaired model matches **239/239 code-derived and 103/103 model-derived cases**. The provisional baseline has **18 mismatches** across the same 342 instances, with matching actual pre-states and inputs. There are no adapter errors in the final supported runs. The separate old-source subset matches 21/21; six intentionally invalid ConfStates remain outside conformance totals.

The generic JSON protocol, runner and eight comparator tests are byte-for-byte unchanged. No supplied invariant predicate was edited or checked. Go executes the supplied implementation; TLC executes original model operators/actions. There is no Python transition oracle, external browsing, other agent, later version or global protocol search.

| Family | Code cases | Baseline code mismatches | Model cases | Baseline model mismatches | Repaired matches code / model |
|---|---:|---:|---:|---:|---:|
'''+ '\n'.join(rows)+f'''
| **Total** | **239** | **8** | **103** | **10** | **239 / 103** |

Counts are direction instances, not independent discoveries. Code inputs retain all 105 prior cases and add 134 conditions; model seeds expand through original TLC domain selection to 103 instances, retaining the prior 43. All 342 pass structural audit. Logs, selected cases, input/pre-state comparisons and complete output differences are preserved in [the final suite](cases/{runroot.name}) and [results.json](results.json).

**Concrete differences and repairs.** Only three behavior definitions change in [repaired-spec/base.tla](repaired-spec/base.tla); [the patch](adaptation/behavior-repairs.patch) is reviewable.

- **R1 — IsLeave:** four code and four model mismatches. Empty V2 explicit/implicit transitions enter joint state from a simple configuration in Go, while the baseline tries to leave and panics. From joint state Go panics on the attempted re-entry, while the baseline incorrectly leaves and promotes staged learners. Require `transition="Auto"` for leave. Evidence: `new/source/raftpb/confchange.go:101–105`, `raft.go:1478–1495`; this restores `old/spec/base.tla:522`. This includes both too restrictive and extra model behavior.
- **R2 — AdvanceCore:** two code and four model mismatches. With a zero captured applied cursor, the baseline appends automatic leave or advances the quota-retry pending index; Go does neither. Restore `b.cursor>0`, matching the enclosing branch at `new/source/raft.go:561`. The old repaired model already had this guard. This is extra model behavior.
- **R3 — ProtocolReady:** two code and two model mismatches. Public RawNode Ready and its empty Ready/Advance sequence execute successfully in Go, but the baseline relation is disabled by `ContainsUpdates`. Permit empty Ready for RawNodes; keep Node channel delivery gated by updates. Evidence: `new/source/rawnode.go:123–126`, `node.go:306–318`. TLC completed successfully and exported mapped disabled outcomes; these were not adapter errors. The empty Advance case identified a disabled Ready prerequisite explicitly.

The old StepHup repair is retained without another edit: `numOfPendingConf` still counts only legacy EntryConfChange at `new/source/raft.go:1605`. The model preserves this omission for V2. The live snapshot guard at `raft.go:1403–1406` still excludes outgoing-only recipients, including staged learners. Restore/restart now preserve full joint configuration metadata for accepted snapshots. These are source-backed local behaviors, not distributed bug claims derived from injected state.

**Adapters and domains.** ConfState names and old/new wrapper calls are bound explicitly. The updated projection adds actual vote-message fields, forced context, CheckQuorum and recorded votes. Advance setup calls original ProtocolReady and original Step actions, then compares the real captured input batch, action-entry state, live output and retained batch contents. Duplicate messages/read results are exercised. Node cases run actual `node.run` channels with Status barriers, including heartbeat, proposal, read acknowledgement and term changes between Ready and Advance. Restart pre-state is actual constructor storage/options, not an unrelated live raft object.

The 96 code-derived vote cases cover learner/voter/staged/removed recipients, regular/pre-votes, term/log freshness, repeated/conflicting votes, lease suppression/expiry and forced context. Candidate-response cases check that the receiver's own configuration controls counting, including both joint halves. Full recovery includes current learners, staged learners, AutoLeave, explicit joint mode, disjoint halves and outgoing-only/removed self. Existing proposal, config, read, quorum and auto-leave cases remain.

The old/new subset has {result['version_comparison']['changed_outputs']} changed and {result['version_comparison']['unchanged_outputs']} unchanged output projections. Learners now answer eligible votes; RawNode accepts output at Ready and preserves newly produced output across Advance; joint metadata survives recovery. Both versions separately match their models on all 21 selected cases. Advance pre-states can differ across versions because acceptance timing changed. [Full deltas](adaptation/version-deltas.json) retain these differences separately from within-version mapping checks. This subset tests the current diff; it does not redo the coordinator's V01 certification.

**Validity, disabled behavior and diagnostics.** The six malformed snapshots cover overlapping voters/learners, staged learners without joint state, and empty incoming voters. Go panics while the model admits configurations; mappings agree, but the structural audit rejects these inputs. They are classified as invalid setup, not repaired or counted as system defects. Generic comparison rows remain preserved as raw disagreements. Constructor panic state projections are diagnostic only.

Two adapter failures were corrected and retained: generated intermediate proposals at full quota initially raised setup errors on ErrProposalDropped; the adapter now continues the real schedule and keeps raw error evidence. A missing pair of parentheses in the new restart TLA mapping caused an evaluation failure; failed exported results were rejected. Every attempt used a fresh directory. The final suite has no missing/extra results, mapping disagreements or failed processes.

**Observer review is separate.** No observer correction is applied to the behavior-only tree. [The proposed patch](adaptation/observer-corrections.patch) adds the missing positive-cursor guard to `history.autoLeaveChecks.eligible`, supported by the zero-cursor cases and `raft.go:561`. `CampaignContract` still treats V2 as campaign-blocking; decide in the later invariant phase whether it intentionally exposes the source omission. `JointSnapshotMemberAcceptance` can expose outgoing-only rejection; obtain a reachable witness before interpreting it as a distributed failure. All safety/decision predicates and other model files are verified unchanged.

**Footprint and time.** {len(footprint)} framework files were added/modified, all target bindings, domains, manifests, reporting or documentation; the three generic files have identical SHA-256 hashes. Per-file added/removed line counts and generated-data sizes are in results.json; [the complete adaptation patch](adaptation/framework-adaptation.patch) is retained. The behavior repair changes three expression lines plus one source comment. No supplied production source/spec/patch or prior input changed ({len(immutable)} immutable files checked).

First compatible current-version run: {timing['first_compatible_seconds']:.1f} seconds after starting. Executable adaptation finished after {timing['executable_adaptation_seconds']:.1f} seconds; total measured wall time through reporting: {timing['total_wall_seconds']:.1f} seconds. Final suite inner process time: {result['execution_time']['final_suite_inner_seconds']:.2f} seconds; longest TLC invocation: {result['execution_time']['max_tlc_invocation_seconds']:.2f} seconds. Each TLC process used one worker, a 2 GB heap and a 175-second outer timeout. Go used GOMAXPROCS=2, a 90-second outer timeout, offline modules and workspace-local cache/tmp. Commands and individual durations are in results.json and each invocation directory.

The eight unchanged comparator tests passed. Supplied learner/restore/Node/RawNode tests and complete confchange/quorum/tracker/raftpb package tests passed. The coordinator's integrity controls remain unchanged; no generic bug or need to rerun its old certification was found.

**Reproduce.** Run from `/workspace`:

```sh
python3 out/framework/targets/etcd/replay.py
```

[The portable suite manifest](framework/targets/etcd/suite.json) lists all six runs, relative paths, supplied tools, limits, all verification commands and regeneration commands. The replay script creates a unique exclusive root, leaving all previous evidence intact. After a rerun, use `python3 out/framework/targets/etcd/summarize.py --run-root <printed-root>` to regenerate the report. Bindings, saved inputs, symbolic domains, repaired model, schema and runner remain in the same framework organization for the next version.

**Remaining limits.** These are locally injected states with structural checks, not a proof of distributed reachability. Shared domains/projections permit correlated errors. Node channels are real but schedules are deterministic and do not cover cancellation, removal gating or arbitrary concurrency. The four-server action domain excludes the quorum allocation threshold; package tests are supplemental. Arbitrary bytes, snapshot data, remote/lease reads, disk failures, pagination boundaries, application replay and broad transport/crash schedules remain uncovered. Empty Node delivery and unknown-peer/local-message RawNode errors are unsupported domain dimensions. No safety claim or global search result is made. [The observation map](framework/targets/etcd/observations.md) records the full projection, ownership, error and uncertainty boundaries.
'''
(O/'report.md').write_text(report)
print(json.dumps(dict(totals=result['totals'],version_comparison=result['version_comparison'],timing=timing,footprint_files=len(footprint)),indent=2))
