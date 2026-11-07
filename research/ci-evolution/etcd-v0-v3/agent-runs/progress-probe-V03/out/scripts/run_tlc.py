import argparse,pathlib,shutil,subprocess,time,json,os
p=argparse.ArgumentParser();p.add_argument('name');p.add_argument('version');p.add_argument('module');p.add_argument('config');p.add_argument('--seconds',type=int,default=90);p.add_argument('--trace',default='joint-autoleave');p.add_argument('--heap',default='4g');a=p.parse_args()
root=pathlib.Path('/workspace'); dest=root/'out/runs'/a.name;dest.mkdir(parents=True,exist_ok=True)
for f in (root/'versions'/a.version/'spec').glob('*'):
 if f.suffix in ('.tla','.cfg'):shutil.copy(f,dest/f.name)
for f in (root/'out/drivers').glob('*'):
 if f.suffix in ('.tla','.cfg'):shutil.copy(f,dest/f.name)
env=os.environ.copy();env['JSON']=str(root/'out'/(a.trace+'-prefix-inputs.ndjson'))
cmd=['timeout','--signal=TERM','--kill-after=5s',str(a.seconds)+'s','java','-Xmx'+a.heap,'-Dtlc2.TLC.progressInterval=10','-cp','/tools/tla2tools.jar:/tools/CommunityModules.jar','tlc2.TLC','-workers','1','-nowarning','-dumpTrace','json','counterexample.json','-config',a.config,a.module]
start=time.time()
with open(dest/'tlc.log','w') as log: r=subprocess.run(cmd,cwd=dest,env=env,stdout=log,stderr=subprocess.STDOUT)
result=dict(name=a.name,version=a.version,module=a.module,config=a.config,seconds_limit=a.seconds,elapsed_seconds=time.time()-start,exit_code=r.returncode,command=cmd,trace=env['JSON'])
json.dump(result,open(dest/'run.json','w'),indent=2);print(json.dumps(result));print((dest/'tlc.log').read_text()[-2500:])
