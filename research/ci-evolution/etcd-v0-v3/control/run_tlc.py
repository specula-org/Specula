"""One bounded experimental TLC campaign with copied, hashed inputs and receipts."""
from pathlib import Path
import argparse, datetime, hashlib, json, re, shutil, subprocess, time
R=Path(__file__).resolve().parents[1]
T=Path('/home/ubuntu/Specula/tools/tlaplus/tlatools/org.lamport.tlatools')
p=argparse.ArgumentParser()
p.add_argument('--spec',required=True);p.add_argument('--module',default='MC');p.add_argument('--config',default='MC.cfg');p.add_argument('--label',required=True)
p.add_argument('--seconds',type=int,default=120);p.add_argument('--workers',type=int,default=2);p.add_argument('--heap',default='6G')
p.add_argument('--coverage',action='store_true');p.add_argument('--simulate',action='store_true');p.add_argument('--depth',type=int,default=500);p.add_argument('--seed',type=int,default=20260922)
a=p.parse_args();assert re.fullmatch(r'[A-Za-z0-9_-]+',a.label)
out=R/'results/exploration'/a.label;out.mkdir(parents=True,exist_ok=False)
spec=out/'spec';spec.mkdir();source=Path(a.spec).resolve()
for f in source.iterdir():
 if f.is_file() and f.suffix in ['.tla','.cfg','.json','.ndjson'] and '_TTrace_' not in f.name:shutil.copy2(f,spec/f.name)
inputs={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in spec.iterdir()}
cmd=['timeout','-s','INT','-k','15s',str(a.seconds)+'s','java','-XX:ActiveProcessorCount=4','-Dtlc2.TLC.progressInterval=10','-XX:+UseParallelGC','-Xmx'+a.heap,'-cp',str(T/'dist/tla2tools.jar')+':'+str(T/'lib/CommunityModules.jar'),'tlc2.TLC','-workers',str(a.workers),'-metadir',str(out/'states'),'-dumpTrace','json',str(out/'counterexample.json'),'-config',a.config]
if a.coverage:cmd+=['-coverage','1']
if a.simulate:cmd+=['-simulate','-depth',str(a.depth),'-seed',str(a.seed)]
cmd+=[a.module]
d={'source_spec':str(source),'input_sha256':inputs,'command':cmd,'cwd':str(spec),'status':'running','budget_seconds':a.seconds,'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat()}
receipt=out/'receipt.json';receipt.write_text(json.dumps(d,indent=2)+'\n')
start=time.monotonic()
with (out/'tlc.log').open('w') as f:
 proc=subprocess.Popen(cmd,cwd=spec,stdout=f,stderr=subprocess.STDOUT);d['pid']=proc.pid;receipt.write_text(json.dumps(d,indent=2)+'\n');code=proc.wait()
s=(out/'tlc.log').read_text();numbers=re.findall(r'([\d,]+) states generated, ([\d,]+) distinct states found, ([\d,]+) states left on queue',s)
progress=[l for l in s.splitlines() if l.startswith('Progress(')]
d.update(status='finished',seconds=time.monotonic()-start,exit_code=code,errors=[l for l in s.splitlines() if l.startswith('Error:')],state_counts=[int(x.replace(',','')) for x in numbers[-1]] if numbers else None,last_progress=progress[-1] if progress else None,completed_no_error='Model checking completed. No error has been found.' in s,exhausted_budget=code in [124,137],counterexample_exists=(out/'counterexample.json').exists())
receipt.write_text(json.dumps(d,indent=2)+'\n');print(json.dumps({k:v for k,v in d.items() if k not in ['input_sha256','command']},indent=2))
