#!/usr/bin/env python3
"""Assemble preserved and source-derived descriptors; never calculate successors."""
import json,pathlib,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[4]
for name in ['domain_v03.py','domain_v03_callbacks.py','domain_v03_boundaries.py','domain_v03_chains.py','domain_v03_post_drop.py','domain_v03_panic_order.py']:
 subprocess.run([sys.executable,str(pathlib.Path(__file__).parent/name)],cwd=R,check=True,timeout=20)
paths=['prior-code-inputs.json','v03-source-inputs.json','v03-callback-inputs.json','v03-boundary-inputs.json','v03-chain-inputs.json','v03-post-drop-inputs.json','v03-panic-order-inputs.json']
xs=sum([json.loads((R/'out/cases'/p).read_text()) for p in paths],[])
(R/'out/cases/code-inputs.json').write_text(json.dumps(xs,indent=2)+'\n')
seeds=json.loads((R/'out/framework/targets/etcd/model-seeds.json').read_text())+json.loads((R/'out/cases/v03-model-seeds.json').read_text())
ids=['v03-config-broadcast-panic-before-transfer','v03-advance-after-drop-raw-14','v03-advance-after-drop-node-17','v03-callback-v2-leave-remove-self','v03-callback-demote-transfer','v03-callback-new-peer','v03-snapshot-advance-raw-cross','v03-empty-log-Leader-apply','v03-empty-log-Leader-apply_then_step','v03-empty-log-Follower-apply_then_step','v03-propose-apply-joint-JointExplicit','v03-propose-apply-simple-JointExplicit','v03-apply-remove-readd-learner-Leader']
seeds += [c for c in xs if c['id'] in ids]
(R/'out/cases/model-seeds.json').write_text(json.dumps(seeds,indent=2)+'\n')
print(json.dumps(dict(source_cases=len(xs),model_seeds=len(seeds))))
