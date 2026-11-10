"""Execute both directions against original Go and TLA+ operations."""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import os
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
FRAME = ROOT / 'framework'
TLC = Path('/home/ubuntu/Specula/tools/tlaplus/tlatools/org.lamport.tlatools/dist/tla2tools.jar')
COMM = Path('/home/ubuntu/Specula/tools/tlaplus/tlatools/org.lamport.tlatools/lib/CommunityModules.jar')

def run(cmd, cwd, log, extra=None):
    start=time.monotonic()
    env=dict(os.environ, GOTOOLCHAIN='local', GOMAXPROCS='2')
    env.update(extra or {})
    with log.open('w') as f:
        result=subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=180)
    receipt={'command':cmd,'cwd':str(cwd),'exit_code':result.returncode,'seconds':time.monotonic()-start,'log':str(log)}
    log.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    if result.returncode: raise RuntimeError(receipt)
    return receipt

def key(row): return json.dumps(row['input'],sort_keys=True)

def normalized(output):
    out=dict(output)
    # Order is abstracted as a message bag. These fixtures send at most one
    # message per destination, so converting the TLA set loses no multiplicity.
    out['messages']=sorted(out['messages'],key=lambda x:json.dumps(x,sort_keys=True))
    return out

def compare(code,model):
    a={key(x):x for x in code};b={key(x):x for x in model}
    if len(a)!=len(code) or len(b)!=len(model) or a.keys()!=b.keys():
        raise ValueError('Duplicate or missing test records')
    return [{'input':a[k]['input'],'code':a[k]['output'],'model':b[k]['output']}
            for k in a if normalized(a[k]['output'])!=normalized(b[k]['output'])]

def model_rows(log):
    rows=[]
    for line in log.read_text().splitlines():
        if line.startswith('"AV_RESULT '):
            rows.append(json.loads(json.loads(line)[len('AV_RESULT '):]))
    if not rows:raise ValueError('No TLC adapter records')
    return rows

def main():
    p=argparse.ArgumentParser();p.add_argument('--version',choices=['V00','V01','V02'],required=True)
    p.add_argument('--label',default='baseline');p.add_argument('--frozen-model',action='store_true');args=p.parse_args()
    version=args.version;work=ROOT/'work'/version;spec=work/'spec';source=work/'source'
    out=ROOT/'results'/('campaign-'+version+'-'+args.label);out.mkdir(exist_ok=False)
    kinds=['Normal','AddVoter']+([] if version=='V00' else ['V2'])
    cases=[dict(zip(['kind','applied','pre_vote','learner'],v))
           for v in itertools.product(kinds,[3,4],[False,True],[False,True])]
    (out/'code-inputs.json').write_text(json.dumps(cases,indent=2)+'\n')
    adapter=(FRAME/'campaign_adapter_test.go.in').read_text().replace('@VOTERS@','Nodes' if version in ('V00','V01') else 'Voters')
    adapter=adapter.replace('@V2_CASE@','' if version=='V00' else '''if c.Kind == "V2" {
        kind=pb.EntryConfChangeV2
        cc:=pb.ConfChangeV2{Changes:[]pb.ConfChangeSingle{{Type:pb.ConfChangeAddNode,NodeID:3}}}
        entryData,err=cc.Marshal();if err!=nil { t.Fatal(err) }
    }''')
    (source/'action_validation_campaign_test.go').write_text(adapter)
    model=(FRAME/'ActionCampaign.tla.in').read_text().replace('@KINDS@','{'+','.join(json.dumps(x) for x in kinds)+'}')
    entry='Entry(1,4,c.kind,0,3,0,1)'
    if version!='V00':entry='IF c.kind="V2" THEN V2Entry(1,4,0,<<Change("AddVoter",3)>>,"Auto",0,1) ELSE '+entry
    model=model.replace('@ENTRY@',entry)
    if args.frozen_model:
        spec=out/'frozen-spec';spec.mkdir()
        shutil.copy2(ROOT/'frozen'/version/'spec/base.tla',spec/'base.tla')
    (spec/'ActionCampaign.tla').write_text(model)
    cfg='''INIT AVInit
NEXT AVNext
CHECK_DEADLOCK FALSE
CONSTANTS
    Server = {1,2,3}
    BootPeers <- DefaultBootPeers
    Joining = {}
    RawNodes = {1,2,3}
    PreVoteNodes = {}
    CheckQuorumNodes = {}
    NoForwardNodes = {}
    RequestId = {1}
    PayloadWeights = {0,1,3}
    EncodedWeights = {1,2}
    ElectionTick = 3
    HeartbeatTick = 1
    MaxInflight = 2
    MaxMsgSize = 1024
    MaxReadySize = 1024
    MaxUncommitted = 1024
    SendPolicy = "Strict"
    PersistPolicy = "Atomic"
    EarlyAdvance = TRUE
    ReadFence = "Inclusive"
    CancelChanges = {}
    CancelUnknownRemovals = TRUE
    RecoveryMode = "Replay"
'''
    receipts=[];result={'version':version,'label':args.label,'directions':{},'scope':'local StepHup projection only'}
    artifacts=out/'artifacts';artifacts.mkdir()
    for f in ['run_campaign.py','ActionCampaign.tla.in','campaign_adapter_test.go.in']:shutil.copy2(FRAME/f,artifacts/f)
    for f in ['base.tla','ActionCampaign.tla']:shutil.copy2(spec/f,artifacts/f)
    shutil.copy2(source/'action_validation_campaign_test.go',artifacts/'action_validation_campaign_test.go')
    result['input_hashes']={str(x):hashlib.sha256(x.read_bytes()).hexdigest() for x in [source/'raft.go',spec/'base.tla',FRAME/'run_campaign.py',source/'action_validation_campaign_test.go',spec/'ActionCampaign.tla']}
    for direction in ('code-driven','model-driven'):
        cpath=out/(direction+'-inputs.json');cpath.write_text(json.dumps(cases))
        config=out/(direction+'.cfg');config.write_text(cfg+'    AVFromFile = '+('TRUE' if direction=='code-driven' else 'FALSE')+'\n    AVInputPath = '+json.dumps(str(cpath))+'\n')
        log=out/(direction+'-model.log')
        receipts.append(run(['java','-Xmx1G','-cp',str(TLC)+':'+str(COMM),'tlc2.TLC','-workers','1','-metadir',str(out/(direction+'-states')),'-config',str(config),'ActionCampaign.tla'],spec,log))
        model=model_rows(log);(out/(direction+'-model.json')).write_text(json.dumps(model,indent=2)+'\n')
        if direction=='model-driven':cpath.write_text(json.dumps([x['input'] for x in model]))
        codepath=out/(direction+'-code.ndjson')
        receipts.append(run(['/usr/local/go/bin/go','test','-count=1','-run','^TestActionValidationCampaign$','-timeout','120s','.'],source,out/(direction+'-code.log'),{'AV_CASES':str(cpath),'AV_OUTPUT':str(codepath)}))
        code=[json.loads(x) for x in codepath.read_text().splitlines()]
        mismatches=compare(code,model)
        result['directions'][direction]={'cases':len(code),'mismatches':mismatches}
    result['receipts']=receipts;(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'result':str(out/'summary.json'),'counts':{k:{'cases':v['cases'],'mismatches':len(v['mismatches'])} for k,v in result['directions'].items()}},ensure_ascii=False))

if __name__=='__main__':main()
