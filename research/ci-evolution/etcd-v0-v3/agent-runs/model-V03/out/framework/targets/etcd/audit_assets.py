"""Integrity and preserved-definition checks; no invariant evaluation."""
import pathlib,re,json,hashlib,difflib
R=pathlib.Path(__file__).resolve().parents[4]
def ops(p):
 s=p.read_text();s=re.sub(r'\(\*.*?\*\)','',s,flags=re.S);s=re.sub(r'\\\*[^\n]*','',s);s=re.sub(r'^RECURSIVE[^\n]*\n','',s,flags=re.M)
 starts=list(re.finditer(r'^([A-Za-z][A-Za-z0-9_]*)(?:\([^\n]*\))?\s*==',s,re.M));d={}
 for i,m in enumerate(starts):
  e=starts[i+1].start() if i+1<len(starts) else s.find('====',m.end());d[m.group(1)]=re.sub(r'\s+','',s[m.start():e if e>=0 else len(s)])
 return d
summary={}
for old in (R/'old/spec').glob('*.tla'):
 new=R/'out/repaired-spec'/old.name;a=ops(old);b=ops(new)
 summary[old.name]=dict(unchanged=[k for k in a if a[k]==b.get(k)],modified=[k for k in a if k in b and a[k]!=b[k]],removed=[k for k in a if k not in b],added=[k for k in b if k not in a])
(R/'out/evidence/operator-inventory.json').write_text(json.dumps(summary,indent=2)+'\n')
assert all(not v['removed'] for v in summary.values())
allowed={'AutoLeaveWeight','AutoLeaveEncoded','AppendEntry','Restore','RewriteConf','ApplyConfCore','ProposalObservation','InitialRaft','AdvanceCore','ProtocolAdvance','ProtocolApplyEntry','RestartCore'}
assert set(summary['base.tla']['modified'])<=allowed
for name in ['VoteContract','CampaignContract','TransferContract','EffectContract','ProposalContract','AutoLeaveAdvance','TypeOK']:
 assert name in summary['base.tla']['unchanged'],name
for old in (R/'old/spec').glob('*.cfg'):
 new=R/'out/repaired-spec'/old.name
 if old.name in ['Trace.cfg','TraceCorrespondence.cfg']:assert old.read_text().split('INVARIANTS')[1]==new.read_text().split('INVARIANTS')[1]
 else:assert old.read_bytes()==new.read_bytes()
for old in (R/'old/spec').iterdir():assert old.read_bytes()==(R/'out/repaired-spec/assets/v02'/old.name).read_bytes()
generic=json.loads((R/'out/evidence/generic-sha256.json').read_text());assert all(hashlib.sha256((R/k).read_bytes()).hexdigest()==v for k,v in generic.items())
manifest=json.loads((R/'input-manifest.json').read_text());bad={};count=0
for k,v in manifest.items():
 if k.startswith(('old/source/','new/source/','old/spec/','new/spec/')) or k in ['update.patch','out/framework/runner.py','out/framework/protocol.schema.json','out/framework/test_runner.py']:
  actual=hashlib.sha256((R/k).read_bytes()).hexdigest();count+=1
  if actual!=v:bad[k]=dict(expected=v,actual=actual)
assert not bad,bad
(R/'out/evidence/input-integrity.json').write_text(json.dumps(dict(checked=count,mismatches=bad,added_source_files=['old/source/action_validation_test.go','new/source/action_validation_test.go'],generic_framework_unchanged=True,original_assets_identical=True,predicate_definitions_preserved=True),indent=2)+'\n')
patch=''
for name in ['base.tla','MC.tla','Update.tla','Trace.tla','Trace.cfg','TraceCorrespondence.cfg']:
 patch+=''.join(difflib.unified_diff((R/'old/spec'/name).read_text().splitlines(True),(R/'out/repaired-spec'/name).read_text().splitlines(True),fromfile='old/spec/'+name,tofile='out/repaired-spec/'+name))
(R/'out/evidence/behavior-and-mapping.patch').write_text(patch)
print(json.dumps(dict(checked_input_hashes=count,source_and_generic_unchanged=True,predicates_preserved=True)))
