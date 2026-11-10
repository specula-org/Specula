#!/usr/bin/env python3
"""Language/system independent action-validation/v1 orchestration and comparison.
Adapters are executable commands; this file has no target semantics/imports.
"""
import argparse,json,pathlib,subprocess,time,collections,sys,re
P=pathlib.Path

def validate_case(c):
 if not isinstance(c,dict) or c.get('protocol')!='action-validation/v1':raise ValueError('invalid protocol envelope')
 if not isinstance(c.get('id'),str) or not re.fullmatch(r'[A-Za-z0-9_.-]+',c['id']):raise ValueError('unsafe/invalid case ID')
 if not isinstance(c.get('action'),str) or not c['action']:raise ValueError('missing action')
 if any(not isinstance(c.get(k),dict) for k in ['pre','input','meta']):raise ValueError('invalid case descriptor')

def read_results(path):
 out={}
 for line in P(path).read_text().splitlines():
  r=json.loads(line)
  if r.get('protocol')!='action-validation/v1' or not isinstance(r.get('id'),str) or not isinstance(r.get('engine'),str):raise ValueError('invalid result envelope')
  if r.get('adapter_status') not in ['ok','error','unsupported']:raise ValueError('invalid adapter status')
  if r['adapter_status']=='ok':
   if not all(k in r for k in ['pre_observation','input_observation','observation']):raise ValueError('incomplete successful observation')
   if not isinstance(r['observation'],dict) or not all(k in r['observation'] for k in ['state','status','return']):raise ValueError('invalid action observation')
  if r['id'] in out:raise ValueError('duplicate result ID '+r['id'])
  out[r['id']]=r
 return out

def norm(x,unordered,path=()):
 if isinstance(x,dict):return {k:norm(v,unordered,path+(k,)) for k,v in sorted(x.items())}
 if isinstance(x,list):
  a=[norm(v,unordered,path+('*',)) for v in x]
  if any(len(q.split('.'))==len(path) and all(s=='*' or s==t for s,t in zip(q.split('.'),path)) for q in unordered):a.sort(key=lambda v:json.dumps(v,sort_keys=True))
  return a
 return x

def differences(a,b,path='$'):
 if type(a)!=type(b):return [dict(path=path,left=a,right=b)]
 if isinstance(a,dict):
  out=[]
  for k in sorted(set(a)|set(b)):
   if k not in a or k not in b:out.append(dict(path=path+'.'+k,left=a.get(k,'<missing>'),right=b.get(k,'<missing>')))
   else:out+=differences(a[k],b[k],path+'.'+k)
  return out
 if isinstance(a,list):
  if len(a)!=len(b):return [dict(path=path,left=a,right=b)]
  return sum((differences(x,y,f'{path}[{i}]') for i,(x,y) in enumerate(zip(a,b))),[])
 return [] if a==b else [dict(path=path,left=a,right=b)]

def compare(cases,left,right,unordered):
 rows=[]
 for c in cases:
  id=c['id'];a=left.get(id);b=right.get(id)
  row=dict(id=id,action=c['action'],verdict='match',pre_differences=[],input_differences=[],differences=[])
  if not a or not b or a.get('adapter_status')!='ok' or b.get('adapter_status')!='ok':row.update(verdict='adapter_error',reason='missing result or adapter-reported error')
  else:
   row['input_differences']=differences(norm(a.get('input_observation'),unordered,('input',)),norm(b.get('input_observation'),unordered,('input',)))
   row['pre_differences']=differences(norm(a['pre_observation'],unordered,('state',)),norm(b['pre_observation'],unordered,('state',)))
   row['differences']=differences(norm(a['observation'],unordered),norm(b['observation'],unordered))
   if row['pre_differences'] or row['input_differences']:row['verdict']='adapter_error'
   elif row['differences']:row['verdict']='behavioral_mismatch'
  rows.append(row)
 return rows

def main():
 p=argparse.ArgumentParser();p.add_argument('--manifest',required=True);p.add_argument('--cases',required=True);p.add_argument('--output',required=True);p.add_argument('--spec',required=True);p.add_argument('--route',choices=['code-to-model','model-to-code'],required=True);a=p.parse_args()
 manifest=json.loads(P(a.manifest).read_text());out=P(a.output).resolve()
 out.mkdir(parents=True,exist_ok=False);commands=[]
 def call(engine,inp,generate=False):
  work=out/engine;result=out/(engine+'.jsonl')
  params=dict(input=str(inp),output=str(result),work=str(work),spec=str(P(a.spec).resolve()))
  cmd=[s.format(**params) for s in manifest[engine]['command']]
  if generate:cmd+=manifest[engine].get('generate_args',[])
  t=time.monotonic()
  with (out/(engine+'.log')).open('w') as f:
   try:r=subprocess.run(cmd,cwd=manifest.get('cwd','/workspace'),stdout=f,stderr=subprocess.STDOUT,timeout=manifest[engine]['timeout_seconds']);code=r.returncode
   except subprocess.TimeoutExpired:code=124
  commands.append(dict(engine=engine,command=cmd,duration_seconds=time.monotonic()-t,exit_code=code))
  return read_results(result) if code==0 and result.exists() else {}
 inp=P(a.cases).resolve()
 for c in json.loads(inp.read_text()):validate_case(c)
 if a.route=='code-to-model':
  cases=json.loads(inp.read_text());left=call('implementation',inp);right=call('model',inp)
 else:
  right=call('model',inp,True);cases=[r['testcase'] for r in right.values()];inp=out/'generated-cases.json';inp.write_text(json.dumps(cases,indent=2));left=call('implementation',inp)
 ids=[c['id'] for c in cases]
 if len(ids)!=len(set(ids)):raise ValueError('duplicate case IDs')
 for c in cases:
  validate_case(c)
 rows=compare(cases,left,right,manifest['unordered_paths'])
 report=dict(protocol='action-validation/v1',route=a.route,spec=a.spec,counts=dict(collections.Counter(r['verdict'] for r in rows)),total=len(rows),commands=commands,results=rows,extra_results=dict(implementation=sorted(set(left)-set(ids)),model=sorted(set(right)-set(ids))))
 (out/'comparison.json').write_text(json.dumps(report,indent=2));print(json.dumps(dict(total=len(rows),counts=report['counts'])))
 if not cases or any(c['exit_code'] for c in commands) or any(report['extra_results'].values()):sys.exit(2)
if __name__=='__main__':main()
