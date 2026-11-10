#!/usr/bin/env python3
"""TLC adapter CLI; original base is copied into an isolated invocation directory."""
import argparse,json,pathlib,shutil,subprocess,time,sys
P=pathlib.Path
here=P(__file__).resolve().parent; root=here.parents[3]
p=argparse.ArgumentParser();p.add_argument('--input',required=True);p.add_argument('--output',required=True);p.add_argument('--spec',required=True);p.add_argument('--work',required=True);p.add_argument('--generate',action='store_true');a=p.parse_args()
work=P(a.work);work.mkdir(parents=True,exist_ok=False);cs=json.loads(P(a.input).read_text());all_results=[];commands=[]
(root/'out/tmp').mkdir(parents=True,exist_ok=True)
for owner in ['raw','node']:
 batch=[c for c in cs if c['action'].endswith('_node')==(owner=='node')]
 if not batch:continue
 d=work/owner;d.mkdir(exist_ok=True);out=d/'results';out.mkdir(exist_ok=True)
 shutil.copy(P(a.spec)/'base.tla',d/'base.tla')
 for name in ['LocalActions.tla','ModelDomains.tla']:shutil.copy(here/name,d/name)
 inp=d/'inputs.json';inp.write_text(json.dumps(batch))
 cfg=(here/'constants.cfg').read_text()+f'\n RawNodes = '+('{1,2,3,4}' if owner=='raw' else '{}')+f'\n InputFile = "{inp}"\n OutputDir = "{out}"\n Generation = '+('TRUE' if a.generate else 'FALSE')+'\n'
 (d/'LocalActions.cfg').write_text(cfg)
 cmd=['/usr/bin/java','-XX:+UseParallelGC','-Xmx2G','-Djava.io.tmpdir='+str(root/'out/tmp'),'-cp','/tools/tla2tools.jar:/tools/CommunityModules.jar','tlc2.TLC','-workers','1','-metadir',str(d/'states'),'-config','LocalActions.cfg','LocalActions']
 start=time.monotonic()
 with (d/'tlc.log').open('w') as f:
  try:r=subprocess.run(cmd,cwd=d,stdout=f,stderr=subprocess.STDOUT,timeout=80);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 commands.append(dict(command=cmd,cwd=str(d),duration_seconds=time.monotonic()-start,exit_code=code))
 if code:
  print((d/'tlc.log').read_text()[-7000:],file=sys.stderr)
  break
 journal=out/'transitions.ndjson'
 groups={}
 if journal.exists():
  for line in journal.read_text().splitlines():
   row=json.loads(line);groups.setdefault(row['id'],{})[json.dumps(row,sort_keys=True)]=row
 results={}
 for ident,values in groups.items():
  if len(values)==1:results[ident]=next(iter(values.values()))
  else:
   results[ident]=dict(protocol='action-validation/v1',id=ident,engine='tlc',adapter_status='unsupported',
    testcase=next(iter(values.values()))['testcase'],reason='Multiple distinct model observations for one fixed action input; refine the observable mapping or support a relation-valued adapter',alternatives=len(values),evidence=str(journal))
 for path in sorted(out.glob('candidate-*.json')):
  seed=json.loads(path.read_text());c=seed['testcase']
  disabled=dict(protocol='action-validation/v1',id=c['id'],engine='tlc',adapter_status='ok',testcase=c,
    pre_observation=seed['pre_observation'],input_observation=seed['input_observation'],
    observation=dict(state=seed['pre_observation'],status='disabled',**{'return':None}),
    reason='Completed finite local relation has no successor from this mapped input',
    disabled_phase=seed.get('setup_phase','tested action'))
  all_results.append(results.get(c['id'],disabled))
# Json has no TLA null value: translate only the adapter sentinel, never integers/sets.
def clean(x):
 if x=='__null__':return None
 if isinstance(x,list):return [clean(v) for v in x]
 if isinstance(x,dict):return {k:clean(v) for k,v in x.items()}
 return x
P(a.output).write_text(''.join(json.dumps(clean(r))+'\n' for r in all_results))
(work/'commands.json').write_text(json.dumps(commands,indent=2))
if any(c['exit_code'] for c in commands):sys.exit(1)
