from pathlib import Path
import subprocess,time,json,sys
cs=[];tag=sys.argv[1]
for v in sys.argv[2:] or ['V01','V02','V03']:
 d=Path('out/revised-spec')/v;cmd=['java','-XX:+UseParallelGC','-Xmx2G','-cp','/tools/tla2tools.jar:/tools/CommunityModules.jar','tlc2.TLC','-workers','1','-config','Witnesses.cfg','Witnesses'];t=time.monotonic()
 with (d/f'witnesses-{tag}.log').open('w') as f:
  try:p=subprocess.run(cmd,cwd=d,stdout=f,stderr=subprocess.STDOUT,timeout=180);code=p.returncode
  except subprocess.TimeoutExpired:code=124
 cs.append(dict(version=v,command=cmd,cwd=str(d),seconds=time.monotonic()-t,exit_code=code,timeout_seconds=180));print(v,code,(d/f'witnesses-{tag}.log').read_text()[-1800:],flush=True)
 Path(f'out/validation/witness-{tag}-commands.json').write_text(json.dumps(cs,indent=2))
