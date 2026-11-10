#!/usr/bin/env python3
"""Summarize saved actual records. No protocol transition calculations."""
import argparse,collections,hashlib,json,pathlib,sys
R=pathlib.Path(__file__).resolve().parents[4];sys.path.insert(0,str(R/'out/framework'))
from runner import read_results,norm,differences
p=argparse.ArgumentParser();p.add_argument('--run-root',default='out/cases/v03-final-03');a=p.parse_args();run=R/a.run_root
unordered=json.loads((R/'out/framework/targets/etcd/manifest.json').read_text())['unordered_paths']
def read(name):return json.loads((run/name).read_text())
comparisons={label:read(label+'/comparison.json') for label in ['baseline-code','baseline-model','repaired-code','repaired-model','old-code','old-model']}
records={label:{e:read_results(run/label/(e+'.jsonl')) for e in ['implementation','model']} for label in comparisons}
source=json.loads((R/'out/cases/code-inputs.json').read_text());generated=read('baseline-model/generated-cases.json')
def ndiff(x,y,part):return differences(norm(x,unordered,part),norm(y,unordered,part))
deltas=[];disagreements=[]
for route,cases in [('code',source),('model',generated)]:
 old=records['old-'+route];new=records['repaired-'+route];baseline=records['baseline-'+route]
 rows={k:{r['id']:r for r in comparisons[k+'-'+route]['results']} for k in ['old','baseline','repaired']}
 for c in cases:
  id=c['id'];og=old['implementation'][id];ng=new['implementation'][id];om=old['model'][id];nm=new['model'][id]
  unsupported=og['adapter_status']=='unsupported'
  pre=ndiff(og.get('pre_observation'),ng.get('pre_observation'),('state',));inp=ndiff(og.get('input_observation'),ng.get('input_observation'),('input',))
  impl=ndiff(og.get('observation'),ng.get('observation'),());mod=ndiff(om.get('observation'),nm.get('observation'),())
  kind='unsupported_old' if unsupported else 'preparation_delta' if pre or inp else 'behavior_changed' if impl else 'unchanged'
  delta=dict(id=id,route=route,action=c['action'],classification=kind,old_source_status=og.get('observation',{}).get('status'),new_source_status=ng.get('observation',{}).get('status'),pre_differences=pre,input_differences=inp,source_differences=impl,model_differences=mod,old_model_verdict=rows['old'][id]['verdict'],baseline_verdict=rows['baseline'][id]['verdict'],repaired_verdict=rows['repaired'][id]['verdict'])
  deltas.append(delta)
  if rows['baseline'][id]['verdict']!='match':
   disagreements.append(dict(id=id,route=route,testcase=c,classification='V03 change plus pre-existing model repair' if impl and rows['old'][id]['verdict']!='match' else 'pre-existing model repair' if not impl and rows['old'][id]['verdict']!='match' else 'V03 behavior change',old_code=og,old_model=om,baseline_new_code=baseline['implementation'][id],inherited_model=baseline['model'][id],repaired_model=nm,comparison=rows['baseline'][id],repaired_comparison=rows['repaired'][id]))
(R/'out/evidence/semantic-deltas.json').write_text(json.dumps(deltas,indent=2)+'\n')
(R/'out/evidence/disagreements.json').write_text(json.dumps(disagreements,indent=2)+'\n')
coverage={}
for route,cases in [('code',source),('model',generated)]:
 rs=records['repaired-'+route]['implementation']
 coverage[route]=dict(total=len(cases),by_action=dict(collections.Counter(c['action'] for c in cases)),statuses=dict(collections.Counter(x['observation']['status'] for x in rs.values())),node_cases=sum(c['action'].endswith('_node') for c in cases),disabled=[id for id,r in rs.items() if r['observation']['status']=='disabled'],panics=[id for id,r in rs.items() if r['observation']['status']=='panic'])
prior=json.loads((R/'out/cases/prior-model-inputs.json').read_text());genby={c['id']:c for c in generated}
prior_replay=dict(total=len(prior),present=sum(c['id'] in genby for c in prior),identical_pre_input=sum(c['id'] in genby and all(c[k]==genby[c['id']][k] for k in ['pre','input','action']) for c in prior))
commands=read('runs.json');nested=[]
for label in comparisons:
 for engine in ['implementation','model']:
  nested += [dict(label=label,engine=engine,**x) for x in read(label+'/'+engine+'/commands.json')]
all_comparisons=[]
for path in sorted((R/'out/cases').rglob('comparison.json')):
 j=json.loads(path.read_text());all_comparisons.append(dict(path=str(path.relative_to(R)),total=j['total'],counts=j['counts'],commands=j['commands']))
final=dict(version_binding=dict(old_source='V02',new_source='V03',inherited_model='old/spec == initial new/spec'),run_root=a.run_root,claim='Local action validation only; no global conformance, distributed reachability or real-bug discovery claim',coverage=coverage,prior_model_reuse=prior_replay,comparisons={k:dict(total=v['total'],counts=v['counts']) for k,v in comparisons.items()},semantic_delta_counts=dict(collections.Counter(d['classification'] for d in deltas)),disagreement_classes=dict(collections.Counter(x['classification'] for x in disagreements)),behavior_repairs=json.loads((R/'out/evidence/triage.json').read_text())['pre_existing_behavior_repairs'],old_unsupported_inputs=[d['id'] for d in deltas if d['classification']=='unsupported_old'],final_pre_input_mapping_disagreements=sum(len(r['pre_differences'])+len(r['input_differences']) for v in comparisons.values() for r in v['results']),commands=commands,engine_commands=nested,verification=read('verification.json'),syntax_preflight=json.loads((R/'out/preflight-03/commands.json').read_text()),input_integrity=json.loads((R/'out/evidence/input-integrity.json').read_text()),evidence=dict(disagreements='out/evidence/disagreements.json',semantic_deltas='out/evidence/semantic-deltas.json',operator_inventory='out/evidence/operator-inventory.json',initial_failures='out/evidence/triage.json',all_runs='out/evidence/run-index.json',original_predicates='out/repaired-spec/assets/v02'))
final['standalone_diagnostic_commands'] = [dict(path=str(p.relative_to(R)),records=json.loads(p.read_text())) for p in [R/'out/evidence/old-binding-initial/commands.json',R/'out/preflight/commands.json',R/'out/preflight-02/commands.json'] if p.exists()]
final['prior_source_reuse'] = dict(cases=239,version_subset=21,unchanged_inputs=True)
(R/'out/evidence/run-index.json').write_text(json.dumps(all_comparisons,indent=2)+'\n')
(R/'out/results.json').write_text(json.dumps(final,indent=2)+'\n')
# Compact actual observation signatures, for selected semantic delta rows.
def sig(r,keys):
 o=r['observation'];s=o['state'];parts=[]
 for key in keys:
  if key=='status':parts.append(o['status'])
  elif key=='lastEntry':parts.append('tail='+s['log'][-1]['kind'] if s['log'] else 'tail=empty')
  elif key=='newPeer':
   p=next((p for p in s['prs'] if p['id']==4),None);parts.append('p4='+('absent' if p is None else f"next {p['next']}, probe {p['probe']}, active {p['active']}"))
  elif key=='self':
   p=next((p for p in s['prs'] if p['id']==1),None);parts.append('self='+('absent' if p is None else f"match {p['match']}/next {p['next']}"))
  elif key=='messages':parts.append('messages='+str(len(s['messages'])))
  else:parts.append(key+'='+str(s[key]))
 return '; '.join(parts)
examples=[('Phase: empty in simple','v03-prop-simple-0-empty-auto',['lastEntry','pending']),('Phase: nonempty in joint','v03-prop-joint-0-v2',['lastEntry','pending']),('Joint explicit empty, then apply','v03-propose-apply-joint-JointExplicit',['status']),('Zero payload over quota','v03-quota-17-two-empty',['status','last','quota']),('Nonempty V2 over quota','v03-quota-17-v2-payload',['status','pending']),('Auto-leave crossing, quota 17','v03-advance-raw-cross-17',['last','pending','quota']),('Auto-leave oldApplied=pending','v03-advance-raw-equal-old-0',['last','pending']),('New peer','v03-apply-new-voter-Leader',['newPeer','messages']),('Probe existing self','v03-probe-existing-self-probe',['messages']),('Demote transferee','v03-apply-demote-Leader',['transfer']),('Bootstrap 3 peers','v03-bootstrap-123',['self']),('Constructor resets progress','v03-construct-joint-2',['self']),('Live snapshot restore','restore-simple',['self']),('Learner remove/re-add','v03-apply-remove-readd-learner-Follower',['newPeer']),('Node V2 self-removal','v03-callback-v2-leave-remove-self',['status']),('Empty-log add then propose','v03-empty-log-Leader-apply_then_step',['status']),('Advance after proposal drop','v03-advance-after-drop-raw-14',['pending','quota','status']),('Panic precedes cancellation','v03-config-broadcast-panic-before-transfer',['transfer','status'])]
lines=['| Boundary / case | V02 Go / inherited model | V03 Go / evolved model |','|---|---|---|']
for label,id,keys in examples:
 vals=[]
 for group in ['old-code','repaired-code']:
  code=sig(records[group]['implementation'][id],keys);model=sig(records[group]['model'][id],keys)
  vals.append(code+(' (both)' if code==model else ' / model: '+model))
 lines.append('| '+label+' (`'+id+'`) | '+vals[0]+' | '+vals[1]+' |')
(R/'out/evidence/semantic-delta-table.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(coverage=coverage,delta_counts=final['semantic_delta_counts'],prior_model_reuse=prior_replay,disagreements=final['disagreement_classes']),indent=2))

from report_v03 import render
render(final,R)
