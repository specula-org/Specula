"""Structural/setup-domain audit, not a protocol transition or safety oracle."""
import json,sys,pathlib,collections

def valid_config(cfg):
 v=set(cfg['voters']);o=set(cfg['outgoing']);l=set(cfg['learners']);n=set(cfg['learnersNext'])
 assert v and not ((v|o)&l) and n<=o and not n&(v|l)
 assert o or (not n and not cfg['autoLeave'])
 for field in ['voters','outgoing','learners','learnersNext']:assert len(cfg[field])==len(set(cfg[field]))

def audit(c):
 valid_config(c['pre']['config'])
 if c['action'] in ['restore','restart']:valid_config(c['input']['snapshot']['config'])
 p=c['pre'];es=p['log'];cfg=p['config'];v=set(cfg['voters']);o=set(cfg['outgoing']);l=set(cfg['learners']);n=set(cfg['learnersNext']);prs=p['prs']
 assert v and not ((v|o)&l) and n<=o and not n&(v|l)
 assert o or (not n and not cfg['autoLeave'])
 assert {pr['id'] for pr in prs}==v|o|l
 assert 0<=p['applied']<=p['commit']<=len(es)
 assert 1<=p['uoff']<=len(es)+1
 assert [e['index'] for e in es]==list(range(1,len(es)+1))
 assert all(es[k]['term']<=es[k+1]['term'] for k in range(len(es)-1))
 assert p['term']>=max([e['term'] for e in es]+[0])
 assert p['quota']<=sum(e['weight'] for e in es[p['applied']:])
 assert all(pr['match']<=len(es) and pr['next']>=0 and len(pr['inflight'])<=2 for pr in prs)
 return c['id']
if __name__=='__main__':
 ids=[];errors=[]
 for path in sys.argv[1:]:
  for c in json.loads(pathlib.Path(path).read_text()):
   try:ids.append(audit(c))
   except Exception as e:errors.append(dict(id=c.get('id'),path=path,error=type(e).__name__))
 print(json.dumps(dict(checked=len(ids)+len(errors),valid=len(ids),errors=errors),indent=2))
 if errors:sys.exit(1)
