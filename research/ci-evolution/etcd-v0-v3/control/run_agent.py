"""Run a fresh experimental agent with only its input packet mounted."""
from pathlib import Path
import argparse
import datetime
import json
import os
import subprocess
import time

ROOT=Path(__file__).resolve().parents[1]
TOOLS=Path('/home/ubuntu/Specula/tools/tlaplus/tlatools/org.lamport.tlatools')

def sandbox(packet):
    cmd=['bwrap','--ro-bind','/usr','/usr','--symlink','usr/bin','/bin',
         '--symlink','usr/lib','/lib','--symlink','usr/lib64','/lib64',
         '--ro-bind','/etc','/etc','--ro-bind',str(Path('/etc/resolv.conf').resolve()),str(Path('/etc/resolv.conf').resolve()),
         '--proc','/proc','--dev','/dev','--tmpfs','/tmp',
         '--dir','/home/ubuntu/.codex','--ro-bind','/home/ubuntu/.codex/auth.json','/home/ubuntu/.codex/auth.json',
         '--ro-bind',str(Path('/home/ubuntu/.local/bin/codex').resolve().parent),'/opt/agent-bin',
         '--ro-bind',str(TOOLS/'dist/tla2tools.jar'),'/tools/tla2tools.jar',
         '--ro-bind',str(TOOLS/'lib/CommunityModules.jar'),'/tools/CommunityModules.jar',
         '--bind',str(packet),'/workspace','--chdir','/workspace',
         '--unshare-pid','--die-with-parent','--new-session',
         '--setenv','PATH','/usr/local/go/bin:/usr/local/bin:/usr/bin:/bin',
         '--setenv','GOTOOLCHAIN','local','--setenv','GOMAXPROCS','2',
         '--setenv','TMPDIR','/tmp','--setenv','GOTMPDIR','/tmp',
         '--setenv','GOCACHE','/tmp/go-build-cache']
    cache=Path('/home/ubuntu/go/pkg/mod')
    if cache.exists():cmd+=['--ro-bind',str(cache),'/cache/go-mod','--setenv','GOMODCACHE','/cache/go-mod']
    return cmd

def main():
    p=argparse.ArgumentParser();p.add_argument('packet');p.add_argument('--model',default='gpt-6-astra')
    p.add_argument('--label',default='attempt-1');p.add_argument('--preflight',action='store_true');args=p.parse_args()
    packet=(ROOT/'agent-runs'/args.packet).resolve();assert packet.is_relative_to(ROOT/'agent-runs')
    cmd=sandbox(packet)
    if args.preflight:
        cmd+=['/opt/agent-bin/codex','--version']
        result=subprocess.run(cmd,timeout=20,capture_output=True,text=True)
        print(json.dumps({'exit_code':result.returncode,'stdout':result.stdout,'stderr':result.stderr}));return
    cmd+=['/opt/agent-bin/codex','exec','--ignore-user-config','--ephemeral',
          '--skip-git-repo-check','--dangerously-bypass-approvals-and-sandbox',
          '-m',args.model,'-c','model_reasoning_effort="xhigh"',
          '-c','web_search="disabled"','-c','features.apps=false','-c','tool_output_token_limit=100000',
          '--json','-o','/workspace/'+args.label+'.final.md','-']
    logfile=ROOT/'logs'/(args.packet+'-'+args.label+'.jsonl');errfile=logfile.with_suffix('.stderr.log')
    receipt={'packet':str(packet),'model':args.model,'effort':'xhigh','started_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'running','log':str(logfile)}
    rpath=logfile.with_suffix('.receipt.json');rpath.write_text(json.dumps(receipt,indent=2)+'\n')
    start=time.monotonic()
    # Preserve the real HOME path; the filesystem view contains only the auth
    # file and this call's ephemeral runtime state. No past sessions or memory.
    env={k:v for k,v in os.environ.items() if not k.startswith(('SPECULA_','CODEX_'))}
    with logfile.open('x') as out,errfile.open('x') as err, (packet/'TASK.md').open() as prompt:
        proc=subprocess.Popen(cmd,stdin=prompt,stdout=out,stderr=err,env=env,start_new_session=True)
        receipt['pid']=proc.pid;rpath.write_text(json.dumps(receipt,indent=2)+'\n')
        result=proc.wait()
    receipt.update(exit_code=result,seconds=time.monotonic()-start,status='finished')
    usage=[]
    for line in logfile.read_text().splitlines():
        try:d=json.loads(line)
        except json.JSONDecodeError:continue
        if d.get('type')=='turn.completed':usage.append(d.get('usage'))
    receipt['usage']=usage;rpath.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))

if __name__=='__main__':main()
