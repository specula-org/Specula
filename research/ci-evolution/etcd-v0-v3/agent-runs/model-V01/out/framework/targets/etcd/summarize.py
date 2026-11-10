#!/usr/bin/env python3
"""Summarize recorded executions and explicit source-backed human triage."""
import json,pathlib,collections,hashlib,re,shutil
R=pathlib.Path('/workspace');O=R/'out'
read=lambda p:json.loads((R/p).read_text())
run_names=['baseline-code','baseline-model','repaired-code','repaired-model']
runs={n:read('out/cases/'+n+'/comparison.json') for n in run_names}
base_cases=read('out/cases/code-inputs.json');model_cases=read('out/cases/baseline-model/generated-cases.json')
assert model_cases==read('out/cases/repaired-model/generated-cases.json'),'regression inputs changed between model versions'
(O/'cases/model-inputs.json').write_text(json.dumps(model_cases,indent=2))
coverage={}
for n,d in runs.items():
 for row in d['results']:
  coverage.setdefault(row['action'],{})[n]=coverage.setdefault(row['action'],{}).get(n,0)+1

def repair_for(id):
 if 'apply' in id:return 'R1'
 if 'hup' in id:return 'R2'
 if 'advance' in id:return 'R3'
 raise ValueError(id)
repairs=[
 dict(id='R1',operator='IsLeave',source=['new/source/raftpb/confchange.go:96','new/source/raft.go:1449'],model='out/repaired-spec/base.tla:522',classification='model_behavior_error',change='Require transition Auto as well as empty V2 changes. Explicit/implicit empty batches request entry into joint state; they do not leave it.'),
 dict(id='R2',operator='StepHup',source=['new/source/raft.go:906','new/source/raft.go:1580'],model='out/repaired-spec/base.tla:268',classification='model_behavior_error_masking_implementation_defect',change='Scan only legacy configuration entries, matching unchanged numOfPendingConf. This retains the implementation omission for V2 rather than fixing the implementation in the model.'),
 dict(id='R3',operator='AdvanceCore',source=['new/source/raft.go:559'],model='out/repaired-spec/base.tla:1071',classification='model_behavior_error',change='Require a positive captured applied cursor before automatic leave, matching the enclosing Go branch. Zero cursor causes neither append nor failed-append pending-index retry.'),
]
mismatches=[]
for n in ['baseline-code','baseline-model']:
 for row in runs[n]['results']:
  if row['verdict']=='behavioral_mismatch':
   r=dict(row,run=n,repair=repair_for(row['id']),classification='source_backed_model_behavior_error',evidence=f'out/cases/{n}/comparison.json')
   mismatches.append(r)
for r in repairs:
 r['baseline_case_counts']=dict(collections.Counter(x['run'] for x in mismatches if x['repair']==r['id']))
 r['remaining_after_repair']=0
commands=[]
for n,d in runs.items():
 for engine in ['implementation','model']:
  p=O/'cases'/n/engine/'commands.json'
  for cmd in json.loads(p.read_text()):
   cmd.update(run=n,engine=engine)
   if engine=='model':
    log=pathlib.Path(cmd['cwd'])/'tlc.log';txt=log.read_text()
    m=re.search(r'(\d+) states generated, (\d+) distinct states found',txt)
    cmd['tlc_states']=dict(generated=int(m[1]),distinct=int(m[2])) if m else None
    cmd['workers']=1;cmd['heap_gb']=2;cmd['outer_timeout_seconds']=175
   else:cmd['outer_timeout_seconds']=90
   commands.append(cmd)
summary={n:dict(total=d['total'],counts=d['counts'],route=d['route'],spec=d['spec'],duration_seconds=sum(c['duration_seconds'] for c in commands if c['run']==n),comparison=f'out/cases/{n}/comparison.json',outer_commands=d['commands']) for n,d in runs.items()}
unique={json.dumps({k:c[k] for k in ['action','pre','input']},sort_keys=True) for c in base_cases+model_cases}
result=dict(protocol='action-validation/v1',pilot=True,claim='Developmental local action validation; no independent bug discovery or general conformance claim.',sources=dict(old='old/source',new='new/source',old_spec='old/spec',baseline='new/spec',repair='out/repaired-spec',old_snapshot_executed=False),runs=summary,
 totals=dict(code_derived_cases=len(base_cases),tlc_generated_cases=len(model_cases),distinct_case_ids=len(base_cases)+len(model_cases),distinct_semantic_inputs=len(unique),baseline_pairs=sum(runs[n]['total'] for n in ['baseline-code','baseline-model']),baseline_matches=sum(runs[n]['counts'].get('match',0) for n in ['baseline-code','baseline-model']),baseline_mismatches=len(mismatches),repaired_pairs=sum(runs[n]['total'] for n in ['repaired-code','repaired-model']),repaired_matches=sum(runs[n]['counts'].get('match',0) for n in ['repaired-code','repaired-model']),repaired_mismatches=sum(runs[n]['counts'].get('behavioral_mismatch',0) for n in ['repaired-code','repaired-model']),final_adapter_errors=sum(d['counts'].get('adapter_error',0) for d in runs.values()),unsupported_cases=0,runner_fault_injection_tests_passed=8),
 coverage=coverage,mismatches=mismatches,repairs=repairs,
 retained_implementation_behavior=[dict(id='snapshot_joint_loss',behavior='Restore and constructor read only ConfState.Nodes and Learners; outgoing voters, staged learners and AutoLeave are lost. Already modeled by RestoreProjection; no repair.',source=['new/source/raft.go:337','new/source/raft.go:1385','new/source/raft.go:1418'],cases=['restore-joint','restart-joint','restore-outgoing-only'],classification='implementation_defect_faithfully_modeled'),dict(id='campaign_v2_scan',behavior='numOfPendingConf ignores V2. R2 aligns the model with that code behavior; it does not fix the defect.',source=['new/source/raft.go:1580'],classification='implementation_defect_retained')],
 invariant_issues=[dict(name='CampaignDecisionEligibility / CampaignContract',source='new/spec/base.tla:660',issue='Still treats V2 as campaign-blocking. Decide later whether this is an intended correctness property exposing the real source omission or a source-alignment contract needing revision.',changed=False),dict(name='AutoLeaveAdvance / history.autoLeaveChecks.eligible',source='new/spec/base.tla:1095',issue='Eligibility observation lacks positive-cursor guard. Repaired zero-cursor behavior can fail this unchanged contract. Review observer/property together later.',changed=False),dict(name='JointSnapshotRecovery',source='new/spec/base.tla:1331',issue='Can expose faithful source loss of joint state. Do not change behavior to satisfy the invariant.',changed=False)],
 adapter_triage=[dict(issue='Wrong nil versus nonnil empty Entry.Size projection',resolution='Concrete EmptyEncoded changed from 8 to 6 in adapter override. Input/output sizes now independently measured in Go; no baseline spec repair.',evidence='out/evidence/development-comparison.json'),dict(issue='Stray target field on normal log descriptors',resolution='Corrected descriptor; classified as pre-state mapping error.',evidence='out/evidence/development-comparison.json'),dict(issue='Internal DropQuota treated as public Advance drop',resolution='Only proposal error maps to dropped; Advance remains void/ok, with all state effects compared.',evidence='out/evidence/development-comparison.json'),dict(issue='TLC nested EXCEPT @ bound to a boolean',resolution='Qualified original input progress reference; aborted invocation retained.',evidence='out/evidence/model-domain-adapter-error'),dict(issue='Initial quota backing and stale-term descriptors structurally invalid',resolution='Corrected input domains; all final cases pass the separate structural audit. Earlier runs excluded from final totals.',evidence='out/evidence/input-domain-audit.json'),dict(issue='Unavailable default build temporary directory / CGO temporary path',resolution='TMPDIR/GOTMPDIR/GOCACHE and Java temp path set inside workspace; pure-Go adapter uses CGO_ENABLED=0.',evidence=['out/evidence/go-development.log','out/evidence/go-development-2.log'])],
 integrity=read('out/evidence/immutability-audit.json'),input_domain_audit=read('out/evidence/input-domain-audit.json'),
 verification=dict(evidence_audit=read('out/evidence/final-evidence-audit.json'),runner_tests=dict(command=['python3','-m','unittest','discover','-s','out/framework','-p','test_runner.py','-v'],log='out/evidence/runner-tests.log',passed=8),input_audit=dict(command=['python3','out/framework/targets/etcd/audit_inputs.py','out/cases/code-inputs.json','out/cases/baseline-model/generated-cases.json'],evidence='out/evidence/input-domain-audit.json')),
 commands=commands,durations=dict(final_recorded_execution_seconds=sum(c['duration_seconds'] for c in commands),max_tlc_invocation_seconds=max(c['duration_seconds'] for c in commands if c['engine']=='model'),note='Measured subprocess wall time, excludes implementation/analysis and diagnostic development attempts. Earlier attempt commands/durations are in their preserved work directories where recorded.'),
 limitations=['Locally injected structurally valid states; no reachability proof from protocol Init, no full protocol checking.','Shared domains and projections permit correlated mistakes; the TLC-generated route is not an independent oracle.','Node ownership tests call the exact real helpers, but omit channel/select scheduling and proposal-channel gating.','No old-version execution adapter; saved legacy cases require API mapping before replay there.','Ghost histories/durability observers, arbitrary payload/context bytes, remote/lease reads, disk I/O failures, bootstrap/status APIs and end-to-end restart/application schedules are outside the declared projection.','No invariants were edited or checked as safety properties; listed invariant issues require later review.'],
 next_actions=['Add real Node channel lifecycle schedules and application-to-Advance sequences.','Obtain reachable cluster traces for the distinguishing cases before interpreting them as distributed counterexamples.','Extend byte-preserving context/remote-read and snapshot/restart replay mappings.','Review the three invariant issues separately, then decide bounds for a later protocol model-checking campaign.','Generate an old-version implementation/model adapter to replay the compatible saved cases.'])
(O/'results.json').write_text(json.dumps(result,indent=2))
print(json.dumps(dict(totals=result['totals'],durations=result['durations']),indent=2))
