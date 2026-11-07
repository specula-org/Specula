from pathlib import Path
import json,importlib.util,subprocess,time,hashlib
R=Path(__file__).resolve().parents[1];P=R/'agent-runs/action-framework-final'
archive=P/'out/archived-pilot-fixtures';archive.mkdir(exist_ok=False)
for v in ['V01','V02']:
 f=P/'versions'/v/'source/action_validation_campaign_test.go';f.rename(archive/(v+'-action_validation_campaign_test.go'))
s=importlib.util.spec_from_file_location('r',R/'control/run_agent.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
rows=[]
for v in ['V01','V02']:
 for route,cases in [('code-to-model','code-inputs.json'),('model-to-code','model-seeds.json')]:
  label=v+'-'+route+'-02';cmd=m.sandbox(P)+['python3','out/framework/runner.py','--manifest','manifests/'+v+'.json','--cases',cases,'--output','out/'+label,'--spec','versions/'+v+'/spec','--route',route]
  st=time.monotonic()
  with (R/'logs'/('action-framework-final-'+label+'.log')).open('w') as f:q=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=200)
  d=json.loads((P/'out'/label/'comparison.json').read_text());row={'version':v,'route':route,'output':'out/'+label,'exit_code':q.returncode,'seconds':time.monotonic()-st,'total':d['total'],'counts':d['counts'],'base_sha256':hashlib.sha256((P/'versions'/v/'spec/base.tla').read_bytes()).hexdigest()};rows.append(row);(P/'out/results-02.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(row),flush=True)
