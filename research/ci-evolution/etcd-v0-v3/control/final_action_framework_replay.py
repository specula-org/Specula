from pathlib import Path
import shutil,json,re,importlib.util,subprocess,time,hashlib
R=Path(__file__).resolve().parents[1];P=R/'agent-runs/action-framework-final';P.mkdir(exist_ok=False)
shutil.copytree(R/'agent-runs/framework-uniqueness-02/out/framework',P/'out/framework',ignore=shutil.ignore_patterns('__pycache__'))
shutil.copytree(R/'agent-runs/model-V03/deps',P/'deps')
for v in ['V01','V02','V03']:
 d=P/'versions'/v;shutil.copytree(R/'work'/v/'source',d/'source',ignore=shutil.ignore_patterns('action_validation*_test.go'))
 f=d/'source/go.mod';f.write_text(re.sub(r'replace go.etcd.io/etcd/pkg => .*','replace go.etcd.io/etcd/pkg => "/workspace/deps/legacy-pkg"',f.read_text()))
 (d/'spec').mkdir();shutil.copy2(R/'work'/v/'spec/base.tla',d/'spec/base.tla')
for name in ['code-inputs.json','model-seeds.json']:shutil.copy2(R/'agent-runs/model-V03/out/cases'/name,P/name)
(P/'manifests').mkdir()
for v in ['V01','V02','V03']:
 d=json.loads((P/'out/framework/targets/etcd/manifest.json').read_text());d['implementation']['command']+=['--source','versions/'+v+'/source'];(P/'manifests'/(v+'.json')).write_text(json.dumps(d,indent=2)+'\n')
s=importlib.util.spec_from_file_location('r',R/'control/run_agent.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
results=[]
for v in ['V01','V02','V03']:
 for route,cases in [('code-to-model','code-inputs.json'),('model-to-code','model-seeds.json')]:
  label=v+'-'+route;cmd=m.sandbox(P)+['python3','out/framework/runner.py','--manifest','manifests/'+v+'.json','--cases',cases,'--output','out/'+label,'--spec','versions/'+v+'/spec','--route',route]
  st=time.monotonic()
  with (R/'logs'/('action-framework-final-'+label+'.log')).open('w') as f:q=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,timeout=200)
  d=json.loads((P/'out'/label/'comparison.json').read_text());row={'version':v,'route':route,'exit_code':q.returncode,'seconds':time.monotonic()-st,'total':d['total'],'counts':d['counts'],'base_sha256':hashlib.sha256((P/'versions'/v/'spec/base.tla').read_bytes()).hexdigest()};results.append(row);(P/'out/results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(row),flush=True)
