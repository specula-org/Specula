"""Prepare an isolated evidence experiment after first decisions have been frozen."""
from pathlib import Path
import json, shutil, hashlib, re
R=Path(__file__).resolve().parents[1]
P=R/'agent-runs/inv-evidence'
P.mkdir(exist_ok=False)
for v in ['V00','V01','V02','V03']:
 d=P/'versions'/v
 shutil.copytree(R/'work'/v/'source',d/'source',ignore=shutil.ignore_patterns('action_validation*_test.go','*.test','go-cache','tmp'))
 (d/'spec').mkdir()
 for f in (R/'work'/v/'spec').iterdir():
  if f.is_file() and f.suffix in ['.tla','.cfg']:shutil.copy2(f,d/'spec'/f.name)
 if v!='V00':shutil.copy2(R/'agent-runs'/('inv-judge-'+v+'-1')/'update.patch',d/'update.patch')
shutil.copytree(R/'agent-runs/model-V03/deps',P/'deps')
for f in P.rglob('source/go.mod'):
 t=re.sub(r'replace go.etcd.io/etcd/pkg => .*','replace go.etcd.io/etcd/pkg => \"/workspace/deps/legacy-pkg\"',f.read_text());f.write_text(t)
(P/'decisions').mkdir()
for v in ['V01','V02','V03']:
 for name in ['decision.json','decision.md']:
  f=R/'agent-runs'/('inv-judge-'+v+'-1')/'out'/name
  if f.exists():shutil.copy2(f,P/'decisions'/(v+'-'+name))
shutil.copytree(R/'agent-runs/model-backward/out/framework',P/'out/framework',ignore=shutil.ignore_patterns('__pycache__'))
(P/'prior-action-evidence').mkdir()
for v in ['V01','V02','V03']:
 src=R/'agent-runs'/('model-'+v)/'out'
 dst=P/'prior-action-evidence'/v;dst.mkdir()
 for name in ['report.md','results.json']:
  shutil.copy2(src/name,dst/name)
 if v=='V03':
  run=json.loads((src/'results.json').read_text())['run_root']
  for label in ['repaired-code','repaired-model','old-code','old-model']:
   d=dst/label;d.mkdir()
   for name in ['implementation.jsonl','model.jsonl','comparison.json']:
    f=src.parent/run/label/name
    if f.exists():shutil.copy2(f,d/name)
  for name in ['code-inputs.json','model-inputs.json','model-seeds.json']:
   f=src/'cases'/name
   if f.exists():shutil.copy2(f,dst/name)
(P/'TASK.md').write_text((R/'prompts/inv-evidence.template.md').read_text()+'''\n\nPacket-specific instructions:\n- versions/V00..V03 contain exact source snapshots and the final local-fidelity models. decisions/V01..V03-* are frozen first judgments, not accepted properties. prior-action-evidence contains real prior local replays, not global reachability.\n- Compare and validate the important update-related decisions, then produce a minimal coherent revised invariant/observer suite for V01, V02, V03 in out/revised-spec/<version>. Preserve all original behavior operators. Behavioral fidelity repairs require a separate source-backed record and action replay. Do not integrate into any repository. Keep historical properties and rejected candidates.\n- Use the actual TLA operators to evaluate truth tables. Save executable TLA witness tests (including old/candidate truth and positive/negative controls), Go replay evidence where representable, exact commands, and machine-readable results. Required focus: joint quorum/campaign/configuration obligations and valid Advance append relaxation for V01; learner vote vs campaign plus Ready/Advance ownership for V02; proposal-phase restrictions, zero-payload admission, auto-leave effect vs ongoing progress, transfer-demotion effects for V03. This focus is validation, not an independent omission-discovery score.\n- Reuse out/framework's generic protocol/runner. Its Go binding supports V01/V02/V03 by detecting the old Node API; V00 may need a small separate native binding or an explicit unsupported comparison. Use --source versions/Vxx/source in per-version manifests. The old adapter's default new/source path does not exist. Its LocalActions tests may omit history/quality for helper calls: do not evaluate vacuous universal invariants.\n- Avoid treating local injected states as globally reachable system bug evidence. Separate pre-existing spec repairs, observer migrations, actual requirement changes, proposed new coverage, and unresolved claims. Model-state outputs at terminal panic have the documented unobservable internal-buffer ordering boundary; never hide pre/input or ordinary messages.\n- No full protocol campaign in this task. Candidate temporal obligations may be drafted for the next search phase, but record liveness as not validated here. Syntax-check the revised suites and make the selected invariant configuration explicit.\n- Finish with out/report.md and out/results.json containing accepted/rejected/unresolved edits, separating witnesses, mutation/nearby negative controls, concrete replay results and limits. Concise reports; full evidence in files.\n''')
manifest={str(f.relative_to(P)):hashlib.sha256(f.read_bytes()).hexdigest() for f in P.rglob('*') if f.is_file()}
(P/'input-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(P)
