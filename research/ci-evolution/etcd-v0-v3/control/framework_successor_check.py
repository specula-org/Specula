"""Expose and prevent silently overwriting multiple model outcomes per case."""
from pathlib import Path
import shutil,json,importlib.util,subprocess,time
R=Path(__file__).resolve().parents[1];P=R/'agent-runs/framework-uniqueness-02';P.mkdir(exist_ok=False)
for name in ['new/source','new/spec','deps','out/framework']:
 shutil.copytree(R/'agent-runs/inv-campaign-control'/name,P/name,ignore=shutil.ignore_patterns('__pycache__'))
cases=json.loads((R/'agent-runs/inv-campaign-control/cases.json').read_text());(P/'cases.json').write_text(json.dumps(cases[:1]))
# Strip coordinator predicate exports; test the ordinary adapter.
f=P/'out/framework/adapters/tla/LocalActions.tla';original=(R/'agent-runs/model-backward/out/framework/adapters/tla/LocalActions.tla').read_text();f.write_text(original)
s=importlib.util.spec_from_file_location('r',R/'control/run_agent.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
def run(label):
 cmd=m.sandbox(P)+['python3','out/framework/runner.py','--manifest','out/framework/targets/etcd/manifest.json','--cases','cases.json','--output','out/'+label,'--spec','new/spec','--route','code-to-model']
 st=time.monotonic()
 with (R/'logs'/(P.name+'-'+label+'.log')).open('w') as out:q=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT,timeout=190)
 d=json.loads((P/'out'/label/'comparison.json').read_text());return {'label':label,'exit_code':q.returncode,'seconds':time.monotonic()-st,'counts':d['counts']}
# Both source-correct and deliberately changed successors are in the relation.
# The older adapter exports both to the same case filename.
fault='''AmbiguousExecute == /\\ phase=0 /\\ phase'=1
 /\\ UNCHANGED <<selected,before,captured,quality,disk,ready,application,requests,wire,history>>
 /\\ \\E c \\in Cases:selected=c /\\ raft'=[raft EXCEPT ![1]=[Core(c,@) EXCEPT !.term=@+1]]
'''
mutated=original.replace('LocalNext == PrepareBoot',fault+'\nLocalNext == AmbiguousExecute \\/ PrepareBoot')
f.write_text(mutated)
results=[run('before-ambiguous')]
# Preserve every completed relation outcome in an append-only invocation journal.
text=original.replace('EXTENDS base, Json','EXTENDS base, Json, IOUtils')
text=text.replace('Emit == IF phase=1 THEN JsonSerialize(OutputDir \\o "/" \\o selected.id \\o ".json",', '''WriteResult(value) == Serialize(<<value>>, OutputDir \\o "/transitions.ndjson",
 [format |-> "NDJSON",openOptions |-> <<"CREATE","APPEND">>,charset |-> "UTF-8"])
Emit == IF phase=1 THEN WriteResult(''')
assert 'WriteResult(value)' in text
f.write_text(text)
f=P/'out/framework/adapters/tla/run.py';runner=f.read_text()
old="results={p.stem:json.loads(p.read_text()) for p in out.glob('*.json') if not p.name.startswith('candidate-')}"
new='''journal=out/'transitions.ndjson'
 groups={}
 if journal.exists():
  for line in journal.read_text().splitlines():
   row=json.loads(line);groups.setdefault(row['id'],{})[json.dumps(row,sort_keys=True)]=row
 results={}
 for ident,values in groups.items():
  if len(values)==1:results[ident]=next(iter(values.values()))
  else:
   results[ident]=dict(protocol='action-validation/v1',id=ident,engine='tlc',adapter_status='unsupported',
    testcase=next(iter(values.values()))['testcase'],reason='Multiple distinct model observations for one fixed action input; refine the observable mapping or support a relation-valued adapter',alternatives=len(values),evidence=str(journal))'''
assert old in runner;f.write_text(runner.replace(old,new))
lf=P/'out/framework/adapters/tla/LocalActions.tla';lf.write_text(text.replace('LocalNext == PrepareBoot',fault+'\nLocalNext == AmbiguousExecute \\/ PrepareBoot'))
results.append(run('after-ambiguous'))
lf.write_text(text);results.append(run('after-deterministic'))
(P/'out/results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
