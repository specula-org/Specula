import json,pathlib,sys,collections,re

def hist(r):
 b=r['usnap']['hist'] if r['usnap']['index'] else r['store']['hist']
 return b[:r['uoff']-1]+r['unstable'] if r['unstable'] else b

def summarize(path):
 d=json.load(open(path));cx=d['counterexample'];out=[];interesting=[]
 prior=None
 for num,s in cx['state']:
  nodes=[]
  for n,r in enumerate(s['raft'],1):
   h=hist(r);ex=[e['index'] for e in h if e['index']>5 and e['kind']=='V2' and not e['changes'] and e['transition']=='Auto']
   appliedex=[e['index'] for e in s['application'][n-1]['hist'] if e['index']>5 and e['kind']=='V2' and not e['changes'] and e['transition']=='Auto']
   nd={k:r[k] for k in ['role','term','lead','applied','commit','pendingConf','config','fatal','quota','readySeq','elapsed','heartbeat']}
   nd.update(node=n,last=len(h),retained_exits=ex,applied_exits=appliedex,app_hist=len(s['application'][n-1]['hist']),ready_active=s['ready'][n-1]['active'],ready_cursor=s['ready'][n-1]['cursor'],jobs=s['application'][n-1]['jobs'])
   nodes.append(nd)
  v={k:s[k] for k in ['l','slot','lastEvent','barrier','transferUsed','earlyUsed','deferNode','tickPending','installed','proposed','completed'] if k in s};v.update(state=num,nodes=nodes)
  out.append(v)
  if prior:
   changes=[]
   for p,q in zip(prior['nodes'],nodes):
    changed=[k for k in ['role','term','applied','commit','pendingConf','config','fatal','retained_exits','applied_exits'] if p[k]!=q[k]]
    if changed:changes.append(dict(node=q['node'],fields=changed))
   if changes or s['lastEvent']['action'] in ['DeferApplication','TransferLeader']:
    interesting.append(dict(state=num,event=s['lastEvent'],changes=changes))
  prior=v
 edges=[dict(source=a[0][0],target=a[2][0],action=a[1]) for a in cx['action']]
 loops=[e for e in edges if e['target']<=e['source']]
 summary=dict(states=len(out),edges=len(edges),loops=loops,events=interesting)
 if loops:
  lo=loops[-1]['target'];period=[s for s in out if s['state']>=lo]
  summary['cycle']=dict(start=lo,length=len(period),actions=dict(collections.Counter(s['lastEvent']['action'] for s in period)),nodes_at_start=period[0]['nodes'],nodes_at_end=period[-1]['nodes'])
 p=pathlib.Path(path).parent
 json.dump(out,open(p/'events.json','w'),indent=2);json.dump(summary,open(p/'summary.json','w'),indent=2)
 print(p.name,len(out),loops)
for arg in sys.argv[1:]:summarize(arg)
