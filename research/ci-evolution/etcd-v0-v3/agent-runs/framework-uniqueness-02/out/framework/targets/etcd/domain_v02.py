"""V02 descriptors only; preserves prior cases and adds diff/consumer boundaries."""
import json,copy,pathlib
from domain import case,cfg,entry,change
R=pathlib.Path(__file__).resolve().parents[4]
def msg(kind='MsgHup',**kw):
 d=dict(type=kind,fromId=2,to=1,term=2,index=0,logTerm=0,commit=0,reject=False,hint=0,context=0,forced=False,entries=[]);d.update(kw);return d
def extend(c):
 c=copy.deepcopy(c);c['pre'].setdefault('checkQuorum',False);c['pre'].setdefault('votes',[])
 for m in c['pre']['messages']:m.setdefault('forced',False)
 c['input'].setdefault('message',msg());c['input'].setdefault('between',[])
 c['meta']['version']='V02';return c
def build():
 xs=[extend(c) for c in json.loads((R/'out/cases/prior-code-inputs.json').read_text())]
 def add(c):c=extend(c);xs.append(c);return c
 # Voting uses actual RawNode.Step. Term and log boundaries, learner/staged/removed roles.
 for name,co in [('learner',cfg((2,3),l=(1,))),('voter',cfg()),('removed',cfg((2,3))),('staged',cfg((2,3),(1,2,3),n=(1,),a=True))]:
  for typ in ['MsgVote','MsgPreVote']:
   for label,kw,pk in [('grant',{},{}),('stale-log',dict(logTerm=1),{}),('short-log',dict(index=1),{}),('higher-log',dict(index=1,logTerm=3),{}),('past-term',dict(term=1),{}),('same-term',dict(term=2),{}),('already-voted',dict(term=2),dict(vote=3)),('repeat-vote',dict(term=2),dict(vote=2,lead=3)),('lease',{},dict(checkQuorum=True,lead=3,elapsed=9)),('lease-expired',{},dict(checkQuorum=True,lead=3,elapsed=10)),('forced',dict(forced=True),dict(checkQuorum=True,lead=3)),('nonmember-candidate',dict(fromId=4),{})]:
    c=add(case(f'vote-{name}-{typ}-{label}','vote',config=co,role='Follower',elapsed=4,**pk) if 'elapsed' not in pk else case(f'vote-{name}-{typ}-{label}','vote',config=co,role='Follower',**pk))
    c['input']['message']=msg(typ,term=3,index=2,logTerm=2);c['input']['message'].update(kw)
 # Unchanged campaign eligibility for learners and staged outgoing voters.
 for label,co in [('learner',cfg((2,3),l=(1,))),('staged',cfg((2,3),(1,2,3),n=(1,),a=True))]:
  for pv in [False,True]:
   add(case(f'hup-v02-{label}-{pv}','hup',config=co,role='Follower',preVote=pv))
 # Candidate tallies use the receiver's configuration, including both voter halves.
 for label,co,frm in [('learner-ignored',cfg(l=(4,)),4),('voter-wins',cfg(l=(4,)),2),('joint-outgoing-only',cfg((1,2),(1,3,4)),3),('joint-incoming-only',cfg((1,2),(1,3,4)),2),('staged-counts',cfg((1,2),(1,2,3),n=(3,),a=True),3)]:
  for reject in [False,True]:
   c=add(case(f'receive-{label}-{reject}','receive',config=co,role='Candidate',vote=1))
   c['pre']['votes']=[dict(id=1,yes=True)]
   c['input']['message']=msg('MsgVoteResp',fromId=frm,reject=reject)
 # Preserve batch content and ownership while real operations emit additional work.
 for owner in ['raw','node']:
  for op in ['heartbeat','proposal','readack','term-change','multiple']:
   c=add(case(f'advance-v02-{owner}-{op}','advance_'+owner,applied=1,uoff=2))
   c['pre']['messages']=[msg('MsgHeartbeat',fromId=1,to=2),msg('MsgHeartbeat',fromId=1,to=2)]
   c['pre']['reads']=[dict(id=7,index=2),dict(id=7,index=2)]
   c['pre']['readQueue']=[dict(id=8,index=2,fromId=1,acks=[1])]
   c['pre']['prevSS']=dict(role='Follower',lead=0)
   operations={'heartbeat':[msg('MsgBeat',fromId=1,term=0)],'proposal':[msg('MsgProp',fromId=1,term=0,entries=[entry(weight=2)])], 'readack':[msg('MsgHeartbeatResp',term=0,context=8)],'term-change':[msg('MsgHeartbeat',fromId=2,term=3,commit=2)]}
   c['input']['between']=sum(operations.values(),[]) if op=='multiple' else operations[op]
 # Empty Ready: RawNode API accepts it; Node has no channel delivery without HasReady.
 add(case('ready-v02-raw-empty','ready_raw',role='Follower'))
 add(case('advance-v02-raw-empty','advance_raw',role='Follower'))
 # Full joint configurations: self learner, staged self, disjoint halves, removed self.
 for name,co in [('full',cfg((1,2),(1,3),l=(4,),n=(3,),a=True)),('full-explicit',cfg((1,2),(1,3),l=(4,),n=(3,))),('staged-self',cfg((2,3),(1,2),l=(4,),n=(1,),a=True)),('learner-self',cfg((2,3),(2,4),l=(1,),n=(4,),a=True)),('disjoint',cfg((1,2),(3,4),a=True)),('removed-self',cfg((2,3),(2,4),n=(4,),a=True))]:
  for act in ['restore','restart']:
   c=add(case(f'{act}-v02-{name}',act,role='Follower'));c['input']['snapshot']['config']=co
 return xs
if __name__=='__main__':
 xs=build();(R/'out/cases/code-inputs.json').write_text(json.dumps(xs,indent=2))
 seeds=[extend(c) for c in json.loads((R/'out/cases/prior-model-seeds.json').read_text())]
 ids=['vote-learner-MsgVote-grant','vote-learner-MsgPreVote-grant','vote-staged-MsgVote-grant','hup-v02-learner-False','advance-v02-raw-multiple','advance-v02-node-multiple','ready-v02-raw-empty','advance-v02-raw-empty','restore-v02-full','restart-v02-full','restore-v02-staged-self','restart-v02-staged-self','restart-v02-learner-self','receive-learner-ignored-False','receive-joint-outgoing-only-False','receive-voter-wins-False']
 seeds += [dict(copy.deepcopy(c),meta=dict(c['meta'],domain='v02')) for c in xs if c['id'] in ids]
 (R/'out/framework/targets/etcd/model-seeds.json').write_text(json.dumps(seeds,indent=2))
 print(len(xs),len(seeds))
