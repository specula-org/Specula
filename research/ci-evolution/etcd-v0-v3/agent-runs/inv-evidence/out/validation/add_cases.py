from pathlib import Path
from copy import deepcopy
import json
p=Path('out/validation/cases.json');cs=json.loads(p.read_text());by={c['id']:c for c in cs}
c=deepcopy(by['v03-advance-raw-equal-old-0']);c['id']='auto-outstanding-leave';c['pre']['log'] += [dict(kind='Normal',target=0,changes=[],transition='Legacy',weight=0,encoded=8,term=2,index=3),dict(kind='V2',target=0,changes=[],transition='Auto',weight=2,encoded=10,term=2,index=4)];c['pre'].update(commit=3,applied=2,pending=2,uoff=5);c['pre']['prevHS']['commit']=3
for pr in c['pre']['prs']:
 pr['next']=5
 if pr['id']==1:pr['match']=4
c['meta']['purpose']='Retain old repeated auto-leave behavior in domain; locally injected outstanding canonical leave.';cs.append(c)
for enough in [False,True]:
 c=deepcopy(by['quorum-joint-1']);c['id']='joint-quorum-'+('sufficient' if enough else 'insufficient');c['action']='receive'
 c['pre']['config']=dict(voters=[1,2],outgoing=[2,3],learners=[],learnersNext=[],autoLeave=False);c['pre'].update(role='Leader',lead=1,commit=1,applied=1)
 c['pre']['prs']=[dict(id=i,match=(2 if i==1 or (enough and i==3) else 1),next=3,mode='Probe',probe=False,pending=0,active=True,inflight=[]) for i in [1,2,3]]
 c['input']['message'].update(type='MsgAppResp',fromId=2,to=1,term=2,index=2,logTerm=0,commit=0,reject=False,hint=0,entries=[])
 c['meta']['purpose']='Actual commit decision under both voter halves; not CheckQuorum stand-in.';cs.append(c)
p.write_text(json.dumps(cs,indent=2));print(len(cs))
