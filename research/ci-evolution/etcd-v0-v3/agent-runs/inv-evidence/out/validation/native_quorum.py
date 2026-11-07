from pathlib import Path
import subprocess,time,json
R=Path('/workspace');d=R/'out/validation/native-quorum';d.mkdir(exist_ok=True)
for src,name in [(R/'versions/V01/spec/base.tla','base.tla'),(R/'out/revised-spec/V01/HistoricalV00.tla','HistoricalV00.tla')]: (d/name).write_text(src.read_text())
s=(R/'out/revised-spec/V01/Witnesses.tla').read_text();defs=s[s.index('FlatR =='):s.index('QC ==')]
body=r'''
OldQ == LET H==INSTANCE HistoricalV00 WITH history <- [H0!EmptyHistory EXCEPT !.commitUses=FlatPost.commitUses] IN H!QuorumAccounting
NewQ == LET H==INSTANCE base WITH history <- [EmptyHistory EXCEPT !.commitUses=JointEnough.commitUses] IN H!QuorumAccounting
InitWitness == /\ marker=0 /\ raft=EmptyFunction /\ disk=EmptyFunction /\ ready=EmptyFunction
 /\ application=EmptyFunction /\ requests=EmptyFunction /\ wire=EmptyBag /\ history=EmptyHistory /\ quality=EmptyQuality
NextWitness == marker'=marker /\ FALSE
Check == /\ Assert(FlatPost.commit=2 /\ JointPost.commit=1 /\ JointEnough.commit=2,"quorum outcomes")
 /\ Assert(FlatPost.commitUses#{} /\ JointEnough.commitUses#{} /\ OldQ /\ NewQ,"nonempty original commit contract")
 /\ JsonSerialize("native-results.json",[oldModel |-> [commit |-> FlatPost.commit,commitUses |-> FlatPost.commitUses,invariant |-> OldQ],
 newModelInsufficient |-> [commit |-> JointPost.commit,commitUses |-> JointPost.commitUses,invariant |-> "no commit event; not vacuous pass"],
 newModelSufficient |-> [commit |-> JointEnough.commit,commitUses |-> JointEnough.commitUses,invariant |-> NewQ],
 oldCode |-> "unsupported native V00 binding; joint state not representable",newCode |-> "replay-V01-observed-07 joint-quorum-insufficient/sufficient"])
============================
'''
(d/'NativeQuorum.tla').write_text('----------- MODULE NativeQuorum -----------\nEXTENDS base, Json\nVARIABLE marker\nH0 == INSTANCE HistoricalV00\n'+defs+body)
cfg=(R/'out/revised-spec/V01/Witnesses.cfg').read_text().replace('WitnessInit','InitWitness').replace('WitnessNext','NextWitness').replace('WitnessCheck','Check')
cfg='\n'.join(x for x in cfg.splitlines() if not any(k in x for k in ['WitnessEmptyEncoded','WitnessBootstrap']))
(d/'NativeQuorum.cfg').write_text(cfg)
cmd=['java','-Xmx2G','-cp','/tools/tla2tools.jar:/tools/CommunityModules.jar','tlc2.TLC','-workers','1','-config','NativeQuorum.cfg','NativeQuorum'];t=time.monotonic()
with (d/'tlc.log').open('w') as f:p=subprocess.run(cmd,cwd=d,stdout=f,stderr=subprocess.STDOUT,timeout=60)
(d/'command.json').write_text(json.dumps(dict(command=cmd,cwd=str(d),seconds=time.monotonic()-t,exit_code=p.returncode),indent=2));print(p.returncode,(d/'tlc.log').read_text()[-1400:])
