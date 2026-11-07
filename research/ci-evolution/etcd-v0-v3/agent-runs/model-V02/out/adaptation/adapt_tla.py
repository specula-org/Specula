from pathlib import Path
p=Path('out/framework/adapters/tla/LocalActions.tla');s=p.read_text()
s=s.replace('VARIABLES selected, phase, before','VARIABLES selected, phase, before, captured')
s=s.replace('!.hint=m.hint,!.context=m.context,!.entries=Ents(m.entries)]','!.hint=m.hint,!.context=m.context,!.forced=m.forced,!.entries=Ents(m.entries)]')
s=s.replace('!.preVote=p.preVote,!.elapsed=p.elapsed','!.preVote=p.preVote,!.checkQuorum=p.checkQuorum,!.elapsed=p.elapsed')
a=s.index('Captured(c) ==');b=s.index('PCfg(c) ==')
s=s[:a]+'''RECURSIVE Between(_, _)
Between(r,ms) == IF ms= <<>> THEN r ELSE Between(Step(r,Msg(Head(ms)),10),Tail(ms))
'''+s[b:]
s=s.replace('hint |-> m.hint,context |-> m.context,entries', 'hint |-> m.hint,context |-> m.context,forced |-> m.forced,entries')
s=s.replace('preVote |-> r.preVote,isLearner','preVote |-> r.preVote,checkQuorum |-> r.checkQuorum,isLearner')
s=s.replace('LocalInit == /\\ selected\\in Cases /\\ phase=0','LocalInit == /\\ selected\\in Cases /\\ phase=IF IsAdvance(selected) THEN -2 ELSE 0\n /\\ captured=EmptyReady')
s=s.replace('Start(selected)', 'Built(selected)')
a=s.index(' /\\ ready=[n\\in Server');b=s.index(' /\\ application=',a)
s=s[:a]+' /\\ ready=[n\\in Server |-> EmptyReady]\n'+s[b:]
s=s.replace('Core(c,r) == CASE c.action="proposal"', 'Core(c,r) == CASE c.action\\in {"vote","receive"} -> Step(r,Msg(c.input.message),10)\n [] c.action="proposal"')
a=s.index('LocalNext ==');b=s.index('Result(c,r) ==')
s=s[:a]+'''\\* Setup uses the actual original Ready action, then original Step calls.
\\* Caller persistence flags and storage installation are environment mappings.
PrepareReady == /\\ phase=-2 /\\ ProtocolReady(1) /\\ phase'=-1
 /\\ captured'=ready'[1] /\\ before'=PState(raft'[1])
 /\\ UNCHANGED <<selected,quality>>
PrepareAdvance == /\\ phase=-1 /\\ phase'=0
 /\\ LET r==raft[1] b==captured
         a==Between([r EXCEPT !.store.hs=IF b.hasHS THEN b.hs ELSE @],selected.input.between)
    IN /\\ raft'=[raft EXCEPT ![1]=a] /\\ before'=PState(a)
 /\\ ready'=[ready EXCEPT ![1].done=Parts(captured),![1].installed=Parts(captured),
              ![1].published=TRUE,![1].queued=TRUE]
 /\\ UNCHANGED <<selected,captured,disk,application,requests,wire,history,quality>>
Execute == /\\ phase=0 /\\ phase'=1 /\\ UNCHANGED <<selected,before,captured,quality>>
 /\\ CASE selected.action\\in {"ready_raw","ready_node"} -> ProtocolReady(1)
    [] IsAdvance(selected) -> ProtocolAdvance(1)
    [] OTHER -> /\\ raft'=[raft EXCEPT ![1]=Core(selected,@)]
                /\\ UNCHANGED <<disk,ready,application,requests,wire,history>>
LocalNext == PrepareReady \\/ PrepareAdvance \\/ Execute
'''+s[b:]
s=s.replace('[] c.action="restore" ->', '[] c.action="restore" ->',1)
s=s.replace('[] OTHER -> "__null__"]','[] IsAdvance(c) -> [batchAfter |-> PReady(captured)]\n [] OTHER -> "__null__"]')
a=s.index('Emit ==')
s=s[:a]+'''PInput(c) == [entries |-> PEnts(Ents(c.input.entries)),entry |-> PEnt(Ent(c.input.entry)),
 snapshot |-> PSnap(Snap(c.input.snapshot)),fromId |-> c.input.fromId,context |-> c.input.context,
 message |-> PMsg(Msg(c.input.message)),
 between |-> [k\\in DOMAIN c.input.between |-> PMsg(Msg(c.input.between[k]))]]
ActualInput(c) == IF IsAdvance(c) THEN PInput(c) @@ [batch |-> PReady(captured)] ELSE PInput(c)
Emit == IF phase=1 THEN JsonSerialize(OutputDir \\o "/" \\o selected.id \\o ".json",
 [protocol |-> "action-validation/v1",id |-> selected.id,engine |-> "tlc",adapter_status |-> "ok",
 testcase |-> selected,pre_observation |-> before,
 input_observation |-> ActualInput(selected),observation |-> Result(selected,raft[1]),raw_fatal |-> raft[1].fatal]) ELSE
 IF phase=0 THEN JsonSerialize(OutputDir \\o "/candidate-" \\o selected.id \\o ".json",
 [testcase |-> selected,pre_observation |-> before,input_observation |-> ActualInput(selected)]) ELSE TRUE
=============================================================================
'''
p.write_text(s)
