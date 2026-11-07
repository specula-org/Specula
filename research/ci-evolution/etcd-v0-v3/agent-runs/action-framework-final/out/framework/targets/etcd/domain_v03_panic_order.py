import sys,json,pathlib
sys.path.insert(0,'out/framework/targets/etcd')
from domain import case,cfg,entry
from domain_v02 import extend
c=extend(case('v03-config-broadcast-panic-before-transfer','apply',config=cfg((1,2,3,4)),applied=1,commit=1,transfer=4))
c['input']['entry']=entry('Remove',4)
c['pre']['prs'][1].update(match=2,next=0,active=True)
c['meta'].update(version='V03',source='switchToConfig maybeCommit -> bcastAppend panic precedes abortLeaderTransfer',reachability='injected zero-Next boundary; no distributed reachability claim')
pathlib.Path('out/cases/v03-panic-order-inputs.json').write_text(json.dumps([c],indent=2)+'\n')
