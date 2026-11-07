from pathlib import Path
import json,shutil,copy,importlib.util,subprocess,time,re
R=Path(__file__).resolve().parents[1];P=R/'agent-runs/inv-campaign-control';P.mkdir(exist_ok=False)
shutil.copytree(R/'work/V03/source',P/'new/source',ignore=shutil.ignore_patterns('action_validation_test.go'))
shutil.copytree(R/'agent-runs/model-V03/deps',P/'deps')
f=P/'new/source/go.mod';f.write_text(re.sub(r'replace go.etcd.io/etcd/pkg => .*','replace go.etcd.io/etcd/pkg => \"/workspace/deps/legacy-pkg\"',f.read_text()))
(P/'new/spec').mkdir()
shutil.copy2(R/'work/V03/spec/base.tla',P/'new/spec/base.tla')
shutil.copytree(R/'agent-runs/model-backward/out/framework',P/'out/framework',ignore=shutil.ignore_patterns('__pycache__'))
cs=json.loads((R/'agent-runs/model-V03/out/cases/code-inputs.json').read_text());cases=[]
for pre in [False,True]:
 c=copy.deepcopy(next(c for c in cs if c['id']=='hup-singleton'));c['id']='joint-self-quorum-'+str(pre);c['pre']['config']['outgoing']=[1];c['pre']['preVote']=pre;c['meta']={'origin':'independent first invariant judgment witness','reachability':'local structurally valid mapped action; not global reachability'};cases.append(c)
 c=copy.deepcopy(next(c for c in cs if c['id']=='hup-V2-'+str(pre)));c['id']='pending-v2-retained-obligation-'+str(pre);cases.append(c)
(P/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
base=(P/'new/spec/base.tla').read_text();original=base[base.index('CampaignContract(o) =='):base.index('TransferObservation(r,target,a) ==')]
candidate=original.replace('CampaignContract(o) ==','CandidateCampaignContract(o) ==').replace('singleton==IsSingleton(o.config)','singleton==JointWon(o.config,{o.node})')
weak=candidate.replace('CandidateCampaignContract(o) ==','WeakCampaignContract(o) ==').replace('o.hist[k].kind\\in ConfKinds','o.hist[k].kind\\in LegacyConfKinds')
f=P/'out/framework/adapters/tla/LocalActions.tla';t=f.read_text();t=t.replace('Emit == IF phase=1 THEN',candidate+'\n'+weak+'\nEmit == IF phase=1 THEN')
t=t.replace('model_witnesses |-> [coreDecision |->', 'model_witnesses |-> [campaignObservation |-> CampaignObservation(Built(selected),raft[1]),\n oldProperty |-> CampaignContract(CampaignObservation(Built(selected),raft[1])),\n candidateProperty |-> CandidateCampaignContract(CampaignObservation(Built(selected),raft[1])),\n legacyOnlyWeakenedProperty |-> WeakCampaignContract(CampaignObservation(Built(selected),raft[1])),\n coreDecision |->')
f.write_text(t)
s=importlib.util.spec_from_file_location('agent_runner',R/'control/run_agent.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
cmd=m.sandbox(P)+['python3','out/framework/runner.py','--manifest','out/framework/targets/etcd/manifest.json','--cases','cases.json','--output','out/replay','--spec','new/spec','--route','code-to-model']
start=time.monotonic()
with (R/'logs/inv-campaign-control.log').open('w') as f:q=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=190)
r={'exit_code':q.returncode,'seconds':time.monotonic()-start,'log':'logs/inv-campaign-control.log'}
if q.returncode==0:
 r['comparison']=json.loads((P/'out/replay/comparison.json').read_text())
 r['truth']=[{'id':d['id'],'source_faithfulness':'see full comparison','old':d['model_witnesses']['oldProperty'],'candidate':d['model_witnesses']['candidateProperty'],'legacy_only_weakening':d['model_witnesses']['legacyOnlyWeakenedProperty'],'observed_after_role':d['model_witnesses']['campaignObservation']['afterRole']} for d in map(json.loads,(P/'out/replay/model.jsonl').read_text().splitlines())]
(P/'out/result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='comparison'},indent=2))
