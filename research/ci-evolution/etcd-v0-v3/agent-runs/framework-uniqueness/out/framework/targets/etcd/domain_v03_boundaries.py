import sys,json,pathlib
sys.path.insert(0,'out/framework/targets/etcd')
from domain import case,cfg,entry,change
from domain_v02 import extend,msg
xs=[]
for owner in ['raw','node']:
 for label,role,pend in [('cross','Leader',2),('no-cross','Leader',0),('follower','Follower',2)]:
  c=extend(case(f'v03-snapshot-advance-{owner}-{label}','advance_'+owner,config=cfg((1,2),(1,2,3),a=True),role=role,applied=1,pending=pend,quota=17,commit=3,log=[entry(index=1,term=2),entry(index=2,term=2),entry(index=3,term=2)],uoff=4))
  c['pre']['usnap']=dict(index=3,term=2,config=c['pre']['config']);xs.append(c)
for role in ['Leader','Follower']:
 for act in ['apply','apply_then_step']:
  c=extend(case(f'v03-empty-log-{role}-{act}',act,role=role,log=[],applied=0,commit=0,uoff=1))
  c['input']['entry']=entry('AddVoter',4)
  c['input']['message']=msg('MsgProp',fromId=1,term=0,entries=[dict(entry(),weight=0,encoded=6)])
  xs.append(c)
for c in xs:c['meta'].update(version='V03',source='advance appliedCursor snapshot; initProgress LastIndex=0 and maybeSendAppend')
pathlib.Path('out/cases/v03-boundary-inputs.json').write_text(json.dumps(xs,indent=2)+'\n')
