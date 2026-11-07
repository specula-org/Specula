"""Replay immutable historical traces after experiment-only model repair."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
import argparse

ROOT=Path(__file__).resolve().parents[1]
PRIOR=Path('/home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260913-175006-a818/etcd-raft/.specula-output')
VERSION='V01'
LIB=Path('/home/ubuntu/Specula/tools/tlaplus/tlatools/org.lamport.tlatools')
OUT=ROOT/'results/trace-V01-campaign-repair'

def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()

def one(trace):
    out=OUT/trace.stem;spec=out/'spec';spec.mkdir(parents=True)
    (out/'traces').mkdir();(out/'traces/trace.ndjson').symlink_to(trace)
    for name in ('base.tla','Trace.tla','TraceCorrespondence.cfg'):
        shutil.copy2(ROOT/'work'/VERSION/'spec'/name,spec/name)
    trace_sha=digest(trace)
    events=sum(1 for _ in trace.open('rb'))
    cmd=['timeout','300s','java','-XX:+UseParallelGC','-Xmx3G','-cp',str(LIB/'dist/tla2tools.jar')+':'+str(LIB/'lib/CommunityModules.jar'),
         'tlc2.TLC','-workers','1','-metadir',str(out/'states'),'-config','TraceCorrespondence.cfg','Trace.tla']
    start=time.monotonic();log=out/'replay.log'
    with log.open('w') as f:
        proc=subprocess.run(cmd,cwd=spec,stdout=f,stderr=subprocess.STDOUT)
    text=log.read_text();counts=re.findall(r'([\d,]+) states generated, ([\d,]+) distinct states found, ([\d,]+) states left on queue',text)
    final=[int(x.replace(',','')) for x in counts[-1]] if counts else None
    success=proc.returncode==0 and 'Model checking completed. No error has been found.' in text and final is not None and final[1]==events
    result={'trace':str(trace),'trace_sha256':trace_sha,'events':events,'fresh_code_execution':False,
            'version':VERSION,'mode':'historical trace regression with the original version-specific correspondence cfg; see that cfg for known-property exclusions',
            'exit_code':proc.returncode,'seconds':time.monotonic()-start,'counts':final,'success':success,'command':cmd,
            'inputs':{p.name:digest(p) for p in spec.iterdir() if p.is_file()},'errors':[x for x in text.splitlines() if x.startswith('Error:')]}
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'trace':trace.name,'success':success,'exit_code':proc.returncode,'seconds':result['seconds'],'errors':result['errors']}),flush=True)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--label',default='campaign-repair')
    parser.add_argument('--version',choices=['V01','V02'],default='V01');args=parser.parse_args()
    assert re.fullmatch(r'[A-Za-z0-9_-]+',args.label)
    VERSION=args.version
    run_id={'V01':'20260913-175006-a818','V02':'20260915-173143-1152'}[VERSION]
    PRIOR=Path('/home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs')/run_id/'etcd-raft/.specula-output'
    OUT=ROOT/'results'/('trace-'+VERSION+'-'+args.label)
    OUT.mkdir(exist_ok=False)
    with ThreadPoolExecutor(max_workers=2) as pool:results=list(pool.map(one,sorted((PRIOR/'traces').glob('*.ndjson'))))
    (OUT/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
