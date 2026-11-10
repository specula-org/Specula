#!/usr/bin/env python3
"""Portable suite orchestration; contains no protocol transitions or expected outputs."""
import argparse,os,json,pathlib,subprocess,sys,time,uuid,datetime
R=pathlib.Path(__file__).resolve().parents[4]
p=argparse.ArgumentParser();p.add_argument('--output-root',default=None);a=p.parse_args()
out=(R/a.output_root) if a.output_root else R/'out/cases'/('v03-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:8])
out.mkdir(parents=True,exist_ok=False)
manifest=R/'out/framework/targets/etcd/suite.json';suite=json.loads(manifest.read_text());records=[]
for run in suite['runs']:
 target=out/run['label']
 cmd=[sys.executable,'out/framework/runner.py','--manifest',run['manifest'],'--cases',run['cases'],'--output',str(target),'--spec',run['spec'],'--route',run['route']]
 start=time.monotonic()
 with (out/(run['label']+'.log')).open('w') as log:r=subprocess.run(cmd,cwd=R,stdout=log,stderr=subprocess.STDOUT,timeout=180)
 records.append(dict(label=run['label'],output=str(target.relative_to(R)),command=cmd,exit_code=r.returncode,duration_seconds=time.monotonic()-start))
 (out/'runs.json').write_text(json.dumps(records,indent=2))
 print(json.dumps(records[-1]),flush=True)
 if r.returncode:sys.exit(r.returncode)
checks=[]
for check in suite.get('verification',[]):
 params=dict(root=str(R),output_root=str(out))
 cmd=[x.format(**params) for x in check['command']]
 env=os.environ.copy();env.update({k:v.format(**params) for k,v in check.get('env',{}).items()})
 start=time.monotonic()
 with (out/(check['name']+'.log')).open('w') as log:r=subprocess.run(cmd,cwd=R/check['cwd'],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=check['timeout_seconds'])
 checks.append(dict(name=check['name'],command=cmd,exit_code=r.returncode,expected_exit=check['expected_exit'],duration_seconds=time.monotonic()-start))
 (out/'verification.json').write_text(json.dumps(checks,indent=2))
 if r.returncode!=check['expected_exit']:sys.exit(2)
print('Reports: '+str(out))
