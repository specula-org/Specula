from pathlib import Path
import subprocess,time,json,sys
R=Path('/workspace');commands=[];tag=sys.argv[1]
for v in sys.argv[2:] or ['V01','V02','V03']:
 cmd=['python3','out/framework/runner.py','--manifest',f'out/validation/manifest-{v}-observed.json','--cases','out/validation/cases.json','--output',f'out/validation/replay-{v}-{tag}','--spec',f'out/revised-spec/{v}','--route','code-to-model']
 start=time.monotonic();p=subprocess.run(cmd,cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
 commands.append(dict(command=cmd,duration_seconds=time.monotonic()-start,exit_code=p.returncode,output=p.stdout));print(v,p.returncode,p.stdout[-1500:],flush=True)
 (R/f'out/validation/observed-{tag}-commands.json').write_text(json.dumps(commands,indent=2))
