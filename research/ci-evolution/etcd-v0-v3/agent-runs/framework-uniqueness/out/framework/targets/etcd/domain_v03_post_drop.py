import sys,json,pathlib
sys.path.insert(0,'out/framework/targets/etcd')
from domain import case,cfg,entry
from domain_v02 import extend,msg
xs=[]
for owner in ['raw','node']:
 for quota in [14,17]:
  c=extend(case(f'v03-advance-after-drop-{owner}-{quota}','advance_'+owner,config=cfg((1,2),(1,2,3),a=True),applied=1,pending=2,quota=quota,uoff=2))
  c['input']['between']=[msg('MsgProp',fromId=1,term=0,entries=[entry(weight=3)])]
  c['meta'].update(version='V03',source='appendEntry return value after an intervening quota-rejected proposal; raft.advance')
  xs.append(c)
pathlib.Path('out/cases/v03-post-drop-inputs.json').write_text(json.dumps(xs,indent=2)+'\n')
