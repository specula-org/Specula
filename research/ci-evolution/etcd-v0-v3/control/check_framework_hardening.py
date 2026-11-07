"""Exercise stale, disabled and failed-export behavior with real TLC/Go adapters."""
from pathlib import Path
import importlib.util
import json
import shutil
import subprocess

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'agent-runs/model-V01-hardened'
s=importlib.util.spec_from_file_location('agent_launcher',ROOT/'control/run_agent.py')
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
OUT=PACKET/'out/negative-controls';OUT.mkdir()
cases=json.loads((PACKET/'out/cases/code-inputs.json').read_text())
case=next(c for c in cases if c['id']=='hup-Normal-False')
(OUT/'input.json').write_text(json.dumps([case]))
adapter=OUT/'disabled-adapter'
shutil.copytree(PACKET/'out/framework/adapters/tla',adapter)
p=adapter/'LocalActions.tla';txt=p.read_text();needle='LocalNext == /\\ phase=0'
assert txt.count(needle)==1;p.write_text(txt.replace(needle,'LocalNext == /\\ FALSE /\\ phase=0'))
results=[]

def call(name,args):
    cmd=m.sandbox(PACKET)+args
    with (OUT/(name+'.log')).open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=120)
    return r.returncode

def tlc(name,adapter_path,work):
    return call(name,['python3',adapter_path,'--input','out/negative-controls/input.json',
      '--output',f'out/negative-controls/{name}.jsonl','--spec','out/repaired-spec','--work',work])

positive=tlc('enabled','out/framework/adapters/tla/run.py','/workspace/out/negative-controls/reused')
refused=tlc('disabled-reused','out/negative-controls/disabled-adapter/run.py','/workspace/out/negative-controls/reused')
fresh=tlc('disabled-fresh','out/negative-controls/disabled-adapter/run.py','/workspace/out/negative-controls/fresh')
read=lambda p:[json.loads(l) for l in p.read_text().splitlines()]
assert positive==0 and refused!=0 and fresh==0
assert not (OUT/'disabled-reused.jsonl').exists()
enabled=read(OUT/'enabled.jsonl');disabled=read(OUT/'disabled-fresh.jsonl')
assert enabled[0]['observation']['status']=='ok'
assert disabled[0]['observation']['status']=='disabled'
assert enabled[0]['pre_observation']==disabled[0]['pre_observation']
assert enabled[0]['input_observation']==disabled[0]['input_observation']
results.append({'control':'stale_successor','positive_exit':positive,'reuse_exit':refused,'fresh_disabled_exit':fresh,'pass':True})

manifest=json.loads((PACKET/'out/framework/targets/etcd/manifest.json').read_text())
model_cmd=manifest['model']['command']
model_cmd=[x.replace('/out/framework/adapters/tla/run.py','/out/negative-controls/disabled-adapter/run.py') for x in model_cmd]
manifest['model']['command']=model_cmd
(OUT/'disabled-manifest.json').write_text(json.dumps(manifest,indent=2))
def runner(name,manifest):
    return call(name,['python3','out/framework/runner.py','--manifest',manifest,'--cases','out/negative-controls/input.json',
      '--output','out/negative-controls/'+name,'--spec','out/repaired-spec','--route','code-to-model'])
code=runner('disabled-comparison','out/negative-controls/disabled-manifest.json')
d=json.loads((OUT/'disabled-comparison/comparison.json').read_text())
assert code==0 and d['counts']=={'behavioral_mismatch':1},d
results.append({'control':'mapped_disabled_vs_concrete_execution','exit_code':code,'counts':d['counts'],'pass':True})

(OUT/'failing_adapter.py').write_text('''from pathlib import Path
import sys
Path(sys.argv[1]).write_bytes(Path('/workspace/out/negative-controls/enabled.jsonl').read_bytes())
raise SystemExit(42)
''')
manifest['model']['command']=['python3','/workspace/out/negative-controls/failing_adapter.py','{output}']
(OUT/'failed-manifest.json').write_text(json.dumps(manifest,indent=2))
code=runner('failed-comparison','out/negative-controls/failed-manifest.json')
d=json.loads((OUT/'failed-comparison/comparison.json').read_text())
assert code==2 and d['counts']=={'adapter_error':1},d
results.append({'control':'failed_command_with_valid_looking_output','exit_code':code,'counts':d['counts'],'pass':True})

code=runner('disabled-comparison','out/negative-controls/disabled-manifest.json')
assert code!=0
results.append({'control':'runner_reused_directory','exit_code':code,'pass':True})
code=call('runner-unit-tests',['python3','-m','unittest','discover','-s','out/framework','-p','test_runner.py','-v'])
assert code==0
results.append({'control':'generic_comparator_unit_tests','exit_code':code,'pass':True})
(OUT/'results.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
