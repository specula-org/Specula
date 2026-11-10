import sys,json,pathlib
sys.path.insert(0,'out/framework/targets/etcd')
from domain import case,cfg,entry,change
from domain_v02 import extend
xs=[]
for name,e,co,tr in [
 ('legacy-remove-self',entry('Remove',1),cfg(),0),
 ('v2-leave-remove-self',entry('V2'),cfg((2,3),(1,2,3)),0),
 ('v2-staged-self',entry('V2',changes=[change('Remove',1)],transition='JointExplicit'),cfg(),0),
 ('demote-self',entry('AddLearner',1),cfg(),0),
 ('demote-transfer',entry('AddLearner',3),cfg(),3),
 ('leave-demote-transfer',entry('V2'),cfg((1,2),(1,2,3),n=(3,),a=True),3),
 ('new-peer',entry('AddVoter',4),cfg(),0),
 ('removed-before',entry('Update',2),cfg((2,3)),0)]:
 e.update(index=2,term=2)
 c=extend(case('v03-callback-'+name,'callback_node',config=co,applied=1,transfer=tr))
 c['input']['entry']=e;c['pre']['log'][1]=e;c['input']['entries']=[dict(entry(),weight=0,encoded=6)]
 c['meta'].update(version='V03',source='node.run confc/propc; raft.applyConfChange/switchToConfig')
 xs.append(c)
p=pathlib.Path('out/cases/v03-callback-inputs.json');p.write_text(json.dumps(xs,indent=2)+'\n')
