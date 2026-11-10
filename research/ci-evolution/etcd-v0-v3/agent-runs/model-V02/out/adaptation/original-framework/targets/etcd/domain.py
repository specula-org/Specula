"""Target-specific finite input descriptors. No Raft transitions or expected values."""
import copy,json,pathlib
ROOT=pathlib.Path('/workspace')
def cfg(v=(1,2,3),o=(),l=(),n=(),a=False):
 return dict(voters=list(v),outgoing=list(o),learners=list(l),learnersNext=list(n),autoLeave=a)
def entry(kind='Normal',target=0,changes=None,transition='Auto',weight=0,index=0,term=0):
 # Size fields are supplied by Go's protobuf encoder before TLC runs; for model
 # generation they are fixed concrete descriptor metadata (verified on replay).
 target=0 if kind in ('Normal','V2') else target
 changes=changes if changes is not None else ([] if kind in ('Normal','V2') else [dict(kind=kind,target=target)])
 if kind=='Normal': w=weight
 elif kind=='V2': w=2+6*len(changes)
 else: w=6
 return dict(kind=kind,target=target,changes=changes,transition=transition if kind=='V2' else 'Legacy',weight=w,encoded=8+w,term=term,index=index)
def change(k,n):return dict(kind=k,target=n)
def case(id,action,config=None,role='Leader',**kw):
 c=config or cfg(); log=[entry(index=1,term=2),entry(index=2,term=2,weight=1)]
 p=dict(config=c,role=role,term=2,vote=0,lead=1 if role=='Leader' else 0,commit=2,applied=2,pending=0,quota=0,transfer=0,log=log,uoff=3,prs=[],messages=[],reads=[],readQueue=[],preVote=False,elapsed=0,heartbeat=0,prevHS=dict(term=2,vote=0,commit=2),prevSS=dict(role=role,lead=1 if role=='Leader' else 0))
 p.update(kw)
 if p['quota']:
  if p['applied']<len(p['log']):
   p['log'][-1].update(weight=p['quota'],encoded=8+p['quota'])
  else:p['log'].append(entry(weight=p['quota'],index=len(p['log'])+1,term=p['term']))
 last=len(p['log'])
 p['prs']=[dict(id=i,match=last if i==1 else 0,next=last+1,mode='Replicate' if i==1 and role=='Leader' else 'Probe',probe=False,pending=0,active=False,inflight=[]) for i in sorted(set(c['voters']+c['outgoing']+c['learners']))]
 return dict(protocol='action-validation/v1',id=id,action=action,pre=p,input=dict(entries=[],entry=entry('V2'),snapshot=dict(index=3,term=3,config=cfg()),fromId=2,context=7),meta=dict(origin='code',reachability='locally valid injected state; no cluster trace claimed'))
def build():
 xs=[]
 def add(c):xs.append(c);return c
 # Proposal admission and bookkeeping before quota rejection, mixed batches.
 for kind in ['AddVoter','V2']:
  for pending,quota,transfer in [(0,0,0),(2,0,0),(0,16,0),(0,0,2)]:
   c=add(case(f'proposal-{kind}-{pending}-{quota}-{transfer}','proposal',applied=1,pending=pending,quota=quota,transfer=transfer))
   c['input']['entries']=[entry(kind,4,[change('AddVoter',4)] if kind=='V2' else None),entry('V2',changes=[change('AddLearner',4)])]
 c=add(case('proposal-removed','proposal',config=cfg((2,3))));c['input']['entries']=[entry('V2',changes=[change('AddVoter',4)])]
 # Configuration application: boundaries and progress lifecycle.
 configs=[('simple',cfg()),('joint',cfg((1,2),(1,2,3),(),(3,),True))]
 operations=[('add',entry('V2',changes=[change('AddVoter',4)])),('demote',entry('V2',changes=[change('AddLearner',3)],transition='JointImplicit')),('replace',entry('V2',changes=[change('Remove',3),change('AddVoter',4)])),('leave',entry('V2')),('empty-explicit',entry('V2',transition='JointExplicit')),('empty-implicit',entry('V2',transition='JointImplicit')),('zero-id',entry('AddVoter',0)),('remove-self',entry('Remove',1)),('remove-transfer',entry('Remove',3)),('remove-readd',entry('V2',changes=[change('Remove',3),change('AddVoter',3)]))]
 for cn,co in configs:
  for en,e in operations:
   c=add(case('apply-'+cn+'-'+en,'apply',config=co,transfer=3));c['input']['entry']=e
   for p in c['pre']['prs']:p.update(match=2,active=True)
 c=add(case('apply-last-voter','apply',config=cfg((1,))));c['input']['entry']=entry('Remove',1)
 # Changed legacy consumers and side effects after reconfiguration.
 for name,kind,target,co in [('legacy-demote','AddLearner',3,cfg()),('unknown-remove','Remove',4,cfg()),('existing-voter','AddVoter',3,cfg()),('new-learner','AddLearner',4,cfg()),('promote-learner','AddVoter',4,cfg(l=(4,))),('update','Update',2,cfg()),('self-demote','AddLearner',1,cfg())]:
  c=add(case('apply-'+name,'apply',config=co));c['input']['entry']=entry(kind,target)
 c=add(case('apply-reduced-quorum-commit','apply',config=cfg((1,2,3,4)),commit=1,applied=1));c['input']['entry']=entry('Remove',4)
 for p in c['pre']['prs']:
  if p['id']==2:p['match']=2
 # Unchanged campaign scan with new entry type.
 for kind in ['Normal','AddVoter','V2']:
  for pre in [False,True]:
   c=add(case(f'hup-{kind}-{pre}','hup',role='Follower',applied=1,preVote=pre));c['pre']['log'][1]=entry(kind,3,[change('AddVoter',3)] if kind=='V2' else None,index=2,term=2)
 for co,name in [(cfg((1,)), 'singleton'),(cfg((1,),(1,2,3)), 'joint-single'),(cfg((2,3),(),(1,)), 'learner'),(cfg((2,3),(1,2,3)), 'outgoing-self')]:
  add(case('hup-'+name,'hup',config=co,role='Follower'))
 # Reads and CheckQuorum exercise both halves, singleton optimization, term fence.
 for name,co in [('simple',cfg()),('singleton',cfg((1,))),('joint',cfg((1,2),(1,3,4))),('joint-single',cfg((1,),(1,2,3)))]:
  for stale in [False,True]:
   c=add(case(f'read-{name}-{stale}','read',config=co));
   if stale:
    for e in c['pre']['log']:e['term']=1
  for active in [(2,),(2,3),()]:
   c=add(case(f'quorum-{name}-{len(active)}','checkquorum',config=co))
   for p in c['pre']['prs']:p['active']=p['id'] in active
 for active in [[1],[1,2]]:
  c=add(case('ack-joint-'+str(len(active)),'readack',config=cfg((1,2),(1,3,4))))
  c['pre']['readQueue']=[dict(id=7,index=2,fromId=1,acks=active)]
  c['input']['fromId']=3
  for p in c['pre']['prs']:p['match']=2
 # Read-only Ready vs Node delivery and matching Advance, zero cursor and quota.
 for owner in ['raw','node']:
  for auto,cursor,quota,role,pending in [(False,2,1,'Leader',2),(True,2,0,'Leader',2),(True,2,16,'Leader',2),(True,0,0,'Leader',0),(True,2,0,'Follower',2),(True,2,0,'Leader',3)]:
   co=cfg((1,2),(1,2,3),(),(),auto) if auto else cfg()
   for act in ['ready','advance']:
    c=add(case(f'{act}-{owner}-{auto}-{cursor}-{quota}-{role}-{pending}',act+'_'+owner,config=co,role=role,applied=0 if cursor else 2,pending=pending,quota=quota,uoff=1))
    c['pre']['messages']=[dict(type='MsgHeartbeat',fromId=1,to=2,term=2,index=0,logTerm=0,commit=0,reject=False,hint=0,context=0,entries=[])]
    c['pre']['reads']=[dict(id=7,index=2)]
    c['pre']['prevHS']=dict(term=1,vote=0,commit=0)
    c['pre']['prevSS']=dict(role='Follower',lead=0)
 # Snapshot/restart source defect retained, inclusion and fast-forward paths.
 for name,co in [('simple',cfg()),('joint',cfg((1,2),(1,2,3),(),(3,),True)),('outgoing-only',cfg((2,3),(1,2,3))),('learner',cfg((2,3),(),(1,)))]:
  for act in ['restore','restart']:
   c=add(case(act+'-'+name,act,role='Follower'));c['input']['snapshot']['config']=co
 for name,index,term,role in [('stale',2,3,'Follower'),('fast-forward',2,2,'Follower'),('non-follower',3,3,'Leader')]:
  c=add(case('restore-'+name,'restore',role=role,commit=1,applied=1));c['input']['snapshot'].update(index=index,term=term)
 xs[-3]['pre']['commit']=2;xs[-3]['pre']['applied']=2
 return xs
if __name__=='__main__':
 p=ROOT/'out/cases/code-inputs.json';p.write_text(json.dumps(build(),indent=2));print(len(build()))
