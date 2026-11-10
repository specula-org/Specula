#!/usr/bin/env python3
import argparse,os,pathlib,subprocess,time,json,shutil,sys
p=argparse.ArgumentParser();p.add_argument('--input',required=True);p.add_argument('--output',required=True);p.add_argument('--work',required=True);p.add_argument('--source',default='new/source');a=p.parse_args();root=pathlib.Path(__file__).resolve().parents[4];work=pathlib.Path(a.work);work.mkdir(parents=True,exist_ok=False)
source=(root/a.source).resolve()
binding=(pathlib.Path(__file__).parent/'action_validation_test.go').read_text()
# Both supplied V02/V03 trees use Voters/VotersOutgoing and node-owned RawNode.
(source/'action_validation_test.go').write_text(binding)
(root/'out/tmp').mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env.update(GOMAXPROCS='2',GOTMPDIR=str(root/'out/tmp'),TMPDIR=str(root/'out/tmp'),GOCACHE=str(root/'out/go-cache'),GOPROXY='off',GOSUMDB='off',GOFLAGS='-mod=readonly',GOTOOLCHAIN='local',CGO_ENABLED='0',AV_INPUT=a.input,AV_OUTPUT=a.output)
cmd=['timeout','90s','/usr/local/go/bin/go','test','-run','^TestActionValidation$','-count=1','-v','.'];start=time.monotonic()
with (work/'go.log').open('w') as f:r=subprocess.run(cmd,cwd=source,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=95)
(work/'commands.json').write_text(json.dumps([dict(command=cmd,cwd=str(source),env={k:env[k] for k in ['GOMAXPROCS','GOTMPDIR','TMPDIR','GOCACHE','GOPROXY','CGO_ENABLED','AV_INPUT','AV_OUTPUT']},duration_seconds=time.monotonic()-start,exit_code=r.returncode)],indent=2));sys.exit(r.returncode)
