import sys,json,pathlib
sys.path.insert(0,'out/framework/targets/etcd')
from domain import case,cfg,entry,change
from domain_v02 import extend
xs=[]
for phase,co in [('simple',cfg()),('joint',cfg((1,2),(1,2,3),a=True))]:
 for transition in ['Auto','JointExplicit','JointImplicit']:
  c=extend(case('v03-propose-apply-'+phase+'-'+transition,'propose_then_apply',config=co))
  c['input']['entries']=[entry('V2',transition=transition)]
  c['meta'].update(version='V03',source='stepLeader len(Changes) gate versus applyConfChange LeaveJoint/EnterJoint')
  xs.append(c)
pathlib.Path('out/cases/v03-chain-inputs.json').write_text(json.dumps(xs,indent=2)+'\n')
