-------------------------- MODULE LocalActions --------------------------
EXTENDS base, Json
CONSTANTS InputFile, OutputDir, Generation
VARIABLES selected, phase, before
LocalEmptyEncoded == 6
InputCases == JsonDeserialize(InputFile)
\* ModelDomains is generated from target descriptors, not transition code.
INSTANCE ModelDomains
Cases == IF Generation THEN ModelCases ELSE SeqSet(InputCases)
Cfg(c) == [voters |-> SeqSet(c.voters), outgoing |-> SeqSet(c.outgoing),
 learners |-> SeqSet(c.learners), learnersNext |-> SeqSet(c.learnersNext),autoLeave |-> c.autoLeave]
Ent(e) == IF e.kind="V2" THEN V2Entry(e.term,e.index,0,e.changes,e.transition,e.weight,e.encoded)
          ELSE Entry(e.term,e.index,e.kind,0,e.target,e.weight,e.encoded)
Ents(es) == [k\in DOMAIN es |-> Ent(es[k])]
Snap(s) == [index |-> s.index, term |-> s.term, config |-> Cfg(s.config),
 hist |-> [k\in 1..s.index |-> Entry(s.term,k,"Normal",0,0,0,8)]]
Msg(m) == [Message(m.type,m.fromId,m.to,m.term) EXCEPT
 !.index=m.index,!.logTerm=m.logTerm,!.commit=m.commit,!.reject=m.reject,
 !.hint=m.hint,!.context=m.context,!.entries=Ents(m.entries)]
Read(s) == [EmptyRead EXCEPT !.id=s.id,!.index=s.index]
ReadQ(s,c) == [EmptyRead EXCEPT !.id=s.id,!.index=s.index,!.requester=s.fromId,
 !.acks=SeqSet(s.acks),!.config=c]
Built(c) == LET p==c.pre h==Ents(p.log) cfg==Cfg(p.config) IN
 [InitialRaft(1,10) EXCEPT !.term=p.term,!.vote=p.vote,!.lead=p.lead,!.role=p.role,
 !.config=cfg,!.cfgHist= <<>>,!.store=Store(h,EmptySnapshot,0,EmptyHS),
 !.unstable=Suffix(h,p.uoff),!.uoff=p.uoff,!.commit=p.commit,!.applied=p.applied,
 !.pendingConf=p.pending,!.quota=p.quota,!.transfer=p.transfer,
 !.prs=[n\in {p.prs[k].id:k\in DOMAIN p.prs} |->
     LET q==CHOOSE x\in SeqSet(p.prs):x.id=n IN
     [Progress(q.match,q.next,q.active) EXCEPT !.mode=q.mode,!.probe=q.probe,
      !.pending=q.pending,!.inflight=q.inflight]],
 !.out=BagSeq([k\in DOMAIN p.messages |-> Msg(p.messages[k])]),
 !.readStates=[k\in DOMAIN p.reads |-> Read(p.reads[k])],
 !.readQueue=[k\in DOMAIN p.readQueue |-> ReadQ(p.readQueue[k],cfg)],
 !.preVote=p.preVote,!.elapsed=p.elapsed,!.heartbeat=p.heartbeat,
 !.prevHS=p.prevHS,!.prevSS=p.prevSS]
IsAdvance(c) == c.action\in {"advance_raw","advance_node"}
Captured(c) == NewReady(Built(c))
Start(c) == LET r==Built(c) b==Captured(c) IN
 IF ~IsAdvance(c) THEN r ELSE [r EXCEPT
 !.store.hs=IF b.hasHS THEN b.hs ELSE @,
 !.out=IF c.action="advance_node" THEN EmptyBag ELSE @,
 !.readStates=IF c.action="advance_node" /\ b.reads# <<>> THEN <<>> ELSE @,
 !.prevSS=IF c.action="advance_node" /\ b.hasSS THEN b.ss ELSE @]
PCfg(c) == c
PEnt(e) == [kind |-> e.kind,transition |-> e.transition,target |-> e.target,
 changes |-> e.changes,weight |-> e.weight,encoded |-> e.encoded,term |-> e.term,index |-> e.index]
PEnts(es) == [k\in DOMAIN es |-> PEnt(es[k])]
PSnap(s) == [index |-> s.index,term |-> s.term,config |-> PCfg(s.config)]
PMsg(m) == [type |-> m.type,fromId |-> m.from,to |-> m.to,term |-> m.term,
 index |-> m.index,logTerm |-> m.logTerm,commit |-> m.commit,reject |-> m.reject,
 hint |-> m.hint,context |-> m.context,entries |-> PEnts(m.entries),snapshot |-> PSnap(m.snapshot)]
RECURSIVE PMsgs(_)
PMsgs(b) == IF b=EmptyBag THEN <<>> ELSE LET m==CHOOSE x\in DOMAIN b:TRUE IN
 <<PMsg(m)>> \o PMsgs(RemoveBag(b,m))
PReads(rs) == [k\in DOMAIN rs |-> [id |-> rs[k].id,index |-> rs[k].index]]
PState(r) == [config |-> PCfg(r.config),role |-> r.role,term |-> r.term,vote |-> r.vote,
 lead |-> r.lead,commit |-> r.commit,applied |-> r.applied,pending |-> r.pendingConf,
 quota |-> r.quota,transfer |-> r.transfer,log |-> PEnts(SubSeq(Hist(r),First(r),Last(r))),
 last |-> Last(r),first |-> First(r),unstable |-> PEnts(r.unstable),uoff |-> r.uoff,
 snapshot |-> PSnap(r.usnap),
 prs |-> {[id |-> n,match |-> r.prs[n].match,next |-> r.prs[n].next,mode |-> r.prs[n].mode,
 probe |-> r.prs[n].probe,pending |-> r.prs[n].pending,active |-> r.prs[n].active,
 inflight |-> r.prs[n].inflight,learner |-> n\in r.config.learners]:n\in DOMAIN r.prs},
 messages |-> PMsgs(r.out),reads |-> PReads(r.readStates),
 readQueue |-> [k\in DOMAIN r.readQueue |-> [id |-> r.readQueue[k].id,index |-> r.readQueue[k].index,
 fromId |-> r.readQueue[k].requester,acks |-> r.readQueue[k].acks]],
 prevHS |-> r.prevHS,prevSS |-> r.prevSS,elapsed |-> r.elapsed,heartbeat |-> r.heartbeat,
 preVote |-> r.preVote,isLearner |-> r.id\in r.config.learners,
 votes |-> {[id |-> n,yes |-> n\in r.yes]:n\in r.yes\cup r.no},
 storage |-> [log |-> PEnts(Suffix(r.store.hist,r.store.cut+1)),snapshot |-> PSnap(r.store.snapshot),
 hs |-> r.store.hs,cut |-> r.store.cut]]
PReady(b) == [hs |-> IF b.hasHS THEN b.hs ELSE EmptyHS,
 ss |-> IF b.hasSS THEN b.ss ELSE "__null__", entries |-> PEnts(b.entries),
 committed |-> PEnts(b.committed),messages |-> PMsgs(b.messages),reads |-> PReads(b.reads),
 snapshot |-> PSnap(b.snapshot),mustSync |-> b.mustSync,cursor |-> b.cursor]
LocalInit == /\ selected\in Cases /\ phase=0
 /\ raft=[n\in Server |-> IF n=1 THEN Start(selected) ELSE InitialRaft(n,10)]
 /\ before=PState(Start(selected))
 /\ disk=[n\in Server |-> IF n=1 /\ selected.action="restart" THEN
       [EmptyDisk EXCEPT !.snapshot=Snap(selected.input.snapshot),
        !.hs=[term |-> 3,vote |-> 0,commit |-> selected.input.snapshot.index]] ELSE EmptyDisk]
 /\ ready=[n\in Server |-> IF n=1 /\ IsAdvance(selected) THEN
       [Captured(selected) EXCEPT !.done=Parts(@),!.installed=Parts(@),!.published=TRUE,!.queued=TRUE]
       ELSE EmptyReady]
 /\ application=[n\in Server |-> EmptyApp]
 /\ requests=[id\in RequestId |-> EmptyRequest]
 /\ wire=EmptyBag /\ history=EmptyHistory /\ quality=EmptyQuality
Core(c,r) == CASE c.action="proposal" -> Step(r,[Message("MsgProp",1,1,0) EXCEPT !.entries=Ents(c.input.entries)],10)
 [] c.action="apply" -> ApplyConfCore(r,Ent(c.input.entry),10)
 [] c.action="hup" -> Step(r,Message("MsgHup",1,1,0),10)
 [] c.action="read" -> Step(r,[Message("MsgReadIndex",1,1,0) EXCEPT !.context=c.input.context],10)
 [] c.action="readack" -> Step(r,[Message("MsgHeartbeatResp",c.input.fromId,1,0) EXCEPT !.context=c.input.context],10)
 [] c.action="checkquorum" -> Step(r,Message("MsgCheckQuorum",1,1,0),10)
 [] c.action="restore" -> Restore(r,Snap(c.input.snapshot),10)
 [] c.action="restart" -> RestartCore(1,10)
LocalNext == /\ FALSE /\ phase=0 /\ phase'=1 /\ UNCHANGED <<selected,before,quality>>
 /\ CASE selected.action\in {"ready_raw","ready_node"} -> ProtocolReady(1)
    [] IsAdvance(selected) -> ProtocolAdvance(1)
    [] OTHER -> /\ raft'=[raft EXCEPT ![1]=Core(selected,@)]
                /\ UNCHANGED <<disk,ready,application,requests,wire,history>>
Result(c,r) == [state |-> PState(r),
 status |-> IF r.fatal#"" THEN "panic" ELSE IF c.action="proposal" /\ r.decision\in {"DropQuota","DropTransfer","DropRemoved"} THEN "dropped" ELSE "ok",
 return |-> IF r.fatal#"" THEN "__null__" ELSE
 CASE c.action="apply" -> PCfg(r.config)
 [] c.action\in {"ready_raw","ready_node"} -> PReady(ready[1])
 [] c.action="restore" -> [restored |-> r.usnap.index=selected.input.snapshot.index /\ r.usnap.index>0]
 [] OTHER -> "__null__"]
Emit == IF phase=1 THEN JsonSerialize(OutputDir \o "/" \o selected.id \o ".json",
 [protocol |-> "action-validation/v1",id |-> selected.id,engine |-> "tlc",adapter_status |-> "ok",
 testcase |-> selected,pre_observation |-> before,
 input_observation |-> [entries |-> PEnts(Ents(selected.input.entries)),entry |-> PEnt(Ent(selected.input.entry)),
 snapshot |-> PSnap(Snap(selected.input.snapshot)),fromId |-> selected.input.fromId,context |-> selected.input.context],observation |-> Result(selected,raft[1]),raw_fatal |-> raft[1].fatal]) ELSE
 JsonSerialize(OutputDir \o "/candidate-" \o selected.id \o ".json",
 [testcase |-> selected,pre_observation |-> before,
 input_observation |-> [entries |-> PEnts(Ents(selected.input.entries)),entry |-> PEnt(Ent(selected.input.entry)),
 snapshot |-> PSnap(Snap(selected.input.snapshot)),fromId |-> selected.input.fromId,context |-> selected.input.context]])
=============================================================================
