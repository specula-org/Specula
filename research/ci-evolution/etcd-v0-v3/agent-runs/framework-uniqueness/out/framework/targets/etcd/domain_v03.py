"""V03 finite input descriptions. No expected transitions or successor oracle."""
import copy,json,pathlib
from domain import case,cfg,entry,change
from domain_v02 import extend,msg
R=pathlib.Path('/workspace')
def empty(kind='Normal'):
 e=entry(kind);e.update(weight=0,encoded=6);return e
def build():
 xs=[]
 def add(c):
  c=extend(c);c['meta'].update(version='V03',origin='source',source='supplied update.patch and changed functions/callers');xs.append(c);return c
 # phase admission uses len(Changes), NOT ConfChangeV2.LeaveJoint.
 for phase,co in [('simple',cfg()),('joint',cfg((1,2),(1,2,3),a=True))]:
  for pending in [0,2,3]:
   for kind,e in [('normal',empty()),('legacy-zero',entry('AddVoter',0)),('legacy',entry('AddVoter',4)),('v2',entry('V2',changes=[change('AddLearner',4)])),('empty-auto',entry('V2')),('empty-nil',empty('V2')),('empty-explicit',entry('V2',transition='JointExplicit')),('empty-implicit',entry('V2',transition='JointImplicit'))]:
    c=add(case(f'v03-prop-{phase}-{pending}-{kind}','proposal',config=co,pending=pending));c['input']['entries']=[e]
  for name,es in [('leave-then-add',[entry('V2'),entry('AddVoter',4)]),('add-then-leave',[entry('AddVoter',4),entry('V2')]),('emptyexplicit-then-leave',[entry('V2',transition='JointExplicit'),entry('V2')]),('normal-then-add',[entry(weight=1),entry('AddVoter',4)])]:
   c=add(case(f'v03-prop-batch-{phase}-{name}','proposal',config=co));c['input']['entries']=es
 for quota in [0,15,16,17]:
  for name,es in [('empty',[empty()]),('two-empty',[empty(),empty()]),('one-byte',[entry(weight=1)]),('large',[entry(weight=17)]),('mixed',[empty(),entry(weight=1)]),('v2-payload',[entry('V2',changes=[change('AddLearner',4)])]),('phase-rewrite',[entry('V2')]),('pending-rewrite',[entry('AddVoter',4)])]:
   c=add(case(f'v03-quota-{quota}-{name}','proposal',quota=quota,pending=3 if name=='pending-rewrite' else 0));c['input']['entries']=es
 # Commit/apply crossing, no crossing, zero cursor, both ownership wrappers.
 for owner in ['raw','node']:
  for label,ap,pc,commit in [('cross',1,2,2),('below',0,3,2),('equal-old',1,1,2),('past',1,0,2),('zero-cursor',2,0,2)]:
   for quota in [0,16,17]:
    c=add(case(f'v03-advance-{owner}-{label}-{quota}','advance_'+owner,config=cfg((1,2),(1,2,3),a=True),applied=ap,pending=pc,commit=commit,quota=quota,uoff=1))
  for label,between in [('term-change',[msg('MsgHeartbeat',term=3,commit=2)]),('new-proposal',[msg('MsgProp',fromId=1,term=0,entries=[empty()])]),('ready-output',[msg('MsgBeat',fromId=1,term=0)])]:
   c=add(case(f'v03-advance-{owner}-{label}','advance_'+owner,config=cfg((1,2),(1,2,3),a=True),applied=1,pending=2,uoff=2));c['input']['between']=between
 # Config change progress and transfer boundaries; unchanged consumers.
 ops=[('new-voter',entry('AddVoter',4),cfg()),('new-learner',entry('AddLearner',4),cfg()),('demote',entry('AddLearner',3),cfg()),('staged-demote',entry('V2',changes=[change('AddLearner',3)],transition='JointImplicit'),cfg()),('leave-demote',entry('V2'),cfg((1,2),(1,2,3),n=(3,),a=True)),('remove-self',entry('Remove',1),cfg()),('demote-self',entry('AddLearner',1),cfg()),('outgoing-self',entry('V2',changes=[change('Remove',1)],transition='JointExplicit'),cfg()),('promote',entry('AddVoter',4),cfg(l=(4,))),('idempotent',entry('AddVoter',2),cfg()),('unknown-remove',entry('Remove',4),cfg()),('update',entry('Update',2),cfg()),('remove-readd-learner',entry('V2',changes=[change('Remove',4),change('AddLearner',4)]),cfg(l=(4,)))]
 for name,e,co in ops:
  for role in ['Leader','Follower']:
   c=add(case(f'v03-apply-{name}-{role}','apply',config=co,role=role,transfer=3));c['input']['entry']=e
 for name,mode,probe,inflight,nxt in [('probe','Probe',False,[],2),('probe-paused','Probe',True,[],2),('replicate','Replicate',False,[],2),('replicate-full','Replicate',False,[1,2],2),('snapshot','Snapshot',False,[],2),('caught-up','Replicate',False,[],3),('self-probe','Probe',False,[],2),('next-zero','Probe',False,[],0)]:
  c=add(case('v03-probe-existing-'+name,'apply'));c['input']['entry']=entry('Update',2)
  p=next(p for p in c['pre']['prs'] if p['id']==(1 if name=='self-probe' else 2));p.update(mode=mode,probe=probe,inflight=inflight,next=nxt)
 for consumer,m in [('heartbeat',msg('MsgBeat',fromId=1,term=0)),('app-reject',msg('MsgAppResp',fromId=4,term=0,index=1,reject=True,hint=0)),('app-success',msg('MsgAppResp',fromId=4,term=0,index=2)),('readack',msg('MsgHeartbeatResp',fromId=2,term=0,context=7)),('quorum',msg('MsgCheckQuorum',fromId=1,term=0)),('transfer',msg('MsgTransferLeader',fromId=3,term=0)),('proposal',msg('MsgProp',fromId=1,term=0,entries=[entry(weight=1)]))]:
  for name,e,co in [ops[0],ops[2],ops[4],ops[6]]:
   c=add(case(f'v03-after-{name}-{consumer}','apply_then_step',config=co,transfer=3));c['input'].update(entry=e,message=m)
 # Direct bootstrap and its actual callers: InitialRaft binds the same peer list.
 for peers in [(1,),(1,2,3),(3,1,2)]:
  for act in ['bootstrap','bootstrap_hup','bootstrap_ready']:
   c=add(case(f'v03-{act}-'+''.join(map(str,peers)),act,role='Follower'));c['input']['snapshot']['config']=cfg(peers)
 # Constructor resets progress after restore; snapshot and suffix boundaries.
 for name,co in [('empty',cfg(())),('simple',cfg()),('learner',cfg((2,3),l=(1,))),('joint',cfg((1,2),(1,3),l=(4,),n=(3,),a=True))]:
  for count in [0,2]:
   c=add(case(f'v03-construct-{name}-{count}','construct',role='Follower'));c['input']['snapshot']=dict(index=0,term=0,config=co);c['input']['entries']=[entry(index=i,term=2) for i in range(1,count+1)]
 for act in ['restore','restart']:
  c=add(case('v03-'+act+'-index-one',act,role='Follower',log=[],commit=0,applied=0,uoff=1));c['input']['snapshot'].update(index=1,term=1)
 # Probe sees compacted tail: !sendIfEmpty returns before snapshot fallback.
 for cut in [1,2]:
  for name,e in [('new',entry('AddVoter',4)),('existing',entry('Update',2))]:
   c=add(case(f'v03-compacted-{cut}-{name}','apply'));c['pre']['cut']=cut;c['pre']['storeSnapshot']=dict(index=cut,term=2,config=cfg());c['input']['entry']=e
   c['pre']['prs'][1].update(next=cut,active=True)
 # Explicit caller preconditions: Node has no Ready delivery when HasReady=false.
 add(case('v03-ready-node-empty','ready_node',role='Follower'))
 add(case('v03-advance-node-empty','advance_node',role='Follower'))
 return xs
if __name__=='__main__':
 xs=build();(R/'out/cases/v03-source-inputs.json').write_text(json.dumps(xs,indent=2)+'\n')
 seeds=[copy.deepcopy(c) for c in xs if c['id'] in ['v03-prop-simple-0-empty-auto','v03-prop-joint-0-v2','v03-prop-joint-0-empty-explicit','v03-quota-17-two-empty','v03-advance-raw-cross-17','v03-advance-node-equal-old-17','v03-apply-new-voter-Leader','v03-apply-demote-Leader','v03-apply-leave-demote-Leader','v03-probe-existing-self-probe','v03-probe-existing-next-zero','v03-bootstrap-123','v03-bootstrap_hup-123','v03-construct-joint-2','v03-compacted-2-new','v03-ready-node-empty','v03-advance-node-empty','v03-after-new-voter-app-reject','v03-after-demote-self-proposal']]
 for c in seeds:c['meta']['origin']='TLC finite input domain'
 (R/'out/cases/v03-model-seeds.json').write_text(json.dumps(seeds,indent=2)+'\n');print(len(xs),len(seeds))
