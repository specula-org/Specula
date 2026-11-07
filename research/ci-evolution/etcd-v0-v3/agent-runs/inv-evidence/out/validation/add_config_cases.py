from pathlib import Path
from copy import deepcopy
import json
p=Path('out/validation/cases.json');cs=json.loads(p.read_text());template=next(c for c in cs if c['id']=='joint-quorum-sufficient')
for good in [False,True]:
 c=deepcopy(template);c['id']='configuration-leave-commit-'+('good' if good else 'bad')
 es=[dict(kind='AddVoter',target=n,changes=[dict(kind='AddVoter',target=n)],transition='Legacy',weight=6,encoded=14,term=1,index=n) for n in [1,2,3]]
 es += [dict(kind='V2',target=0,changes=[dict(kind='Remove',target=3),dict(kind='AddVoter',target=4)],transition='JointExplicit',weight=14,encoded=22,term=2,index=4),dict(kind='V2',target=0,changes=[],transition='Auto',weight=2,encoded=10,term=2,index=5)]
 c['pre'].update(log=es,commit=4,applied=4,pending=5,uoff=6,quota=0,role='Leader',lead=1)
 c['pre']['config']=dict(voters=[1,2,4],outgoing=[1,2,3] if good else [],learners=[],learnersNext=[],autoLeave=False)
 members=[1,2,3,4] if good else [1,2,4]
 c['pre']['prs']=[dict(id=n,match=5 if n!=4 else 4,next=6,mode='Probe',probe=False,pending=0,active=True,inflight=[]) for n in members]
 c['input']['message'].update(fromId=4,index=5)
 c['meta']['purpose']='Original commit transition with complete predecessor versus intentionally premature final config; no global reachability claim.'
 cs.append(c)
p.write_text(json.dumps(cs,indent=2))
