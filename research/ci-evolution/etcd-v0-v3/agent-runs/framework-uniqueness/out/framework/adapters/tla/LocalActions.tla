-------------------------- MODULE LocalActions --------------------------
EXTENDS base, Json, IOUtils
CONSTANTS InputFile, OutputDir, Generation
VARIABLES selected, phase, before, captured
LocalEmptyEncoded == 6
LocalBootstrapPayload == 6
LocalBootstrapEncoded == 14
BootState(c) ==
 LET peers==c.input.snapshot.config.voters
     joining==Server \ SeqSet(peers)
     B==INSTANCE base WITH BootPeers <- peers, Joining <- joining
 IN B!InitialRaft(1,10)
StorageCut(p) == IF "cut" \in DOMAIN p THEN p.cut ELSE 0
IsBoot(c) == c.action \in {"bootstrap","bootstrap_hup","bootstrap_ready"}
IsConstruct(c) == c.action \in {"restart","construct"}
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
StorageSnap(p) == IF "storeSnapshot" \in DOMAIN p THEN Snap(p.storeSnapshot) ELSE EmptySnapshot
Msg(m) == [Message(m.type,m.fromId,m.to,m.term) EXCEPT
 !.index=m.index,!.logTerm=m.logTerm,!.commit=m.commit,!.reject=m.reject,
 !.hint=m.hint,!.context=m.context,!.forced=m.forced,!.entries=Ents(m.entries)]
Read(s) == [EmptyRead EXCEPT !.id=s.id,!.index=s.index]
ReadQ(s,c) == [EmptyRead EXCEPT !.id=s.id,!.index=s.index,!.requester=s.fromId,
 !.acks=SeqSet(s.acks),!.config=c]
Built(c) == LET p==c.pre h==Ents(p.log) cfg==Cfg(p.config) IN
 [InitialRaft(1,10) EXCEPT !.term=p.term,!.vote=p.vote,!.lead=p.lead,!.role=p.role,
 !.yes={p.votes[k].id:k\in {i\in DOMAIN p.votes:p.votes[i].yes}},
 !.no={p.votes[k].id:k\in {i\in DOMAIN p.votes:~p.votes[i].yes}},
 !.config=cfg,!.cfgHist= <<>>,!.store=Store(h,StorageSnap(p),StorageCut(p),EmptyHS),
 !.usnap=IF "usnap" \in DOMAIN p THEN Snap(p.usnap) ELSE EmptySnapshot,
 !.unstable=Suffix(h,p.uoff),!.uoff=p.uoff,!.commit=p.commit,!.applied=p.applied,
 !.pendingConf=p.pending,!.quota=p.quota,!.transfer=p.transfer,
 !.prs=[n\in {p.prs[k].id:k\in DOMAIN p.prs} |->
     LET q==CHOOSE x\in SeqSet(p.prs):x.id=n IN
     [Progress(q.match,q.next,q.active) EXCEPT !.mode=q.mode,!.probe=q.probe,
      !.pending=q.pending,!.inflight=q.inflight]],
 !.out=BagSeq([k\in DOMAIN p.messages |-> Msg(p.messages[k])]),
 !.readStates=[k\in DOMAIN p.reads |-> Read(p.reads[k])],
 !.readQueue=[k\in DOMAIN p.readQueue |-> ReadQ(p.readQueue[k],cfg)],
 !.preVote=p.preVote,!.checkQuorum=p.checkQuorum,!.elapsed=p.elapsed,!.heartbeat=p.heartbeat,
 !.prevHS=p.prevHS,!.prevSS=p.prevSS,!.nodeLead=p.lead,!.propcEnabled=p.lead#0]
IsAdvance(c) == c.action\in {"advance_raw","advance_node"}
RECURSIVE Between(_, _)
Between(r,ms) == IF ms= <<>> THEN r ELSE Between(Step(r,Msg(Head(ms)),10),Tail(ms))
PCfg(c) == c
PEnt(e) == [kind |-> e.kind,transition |-> e.transition,target |-> e.target,
 changes |-> e.changes,weight |-> e.weight,encoded |-> e.encoded,term |-> e.term,index |-> e.index]
PEnts(es) == [k\in DOMAIN es |-> PEnt(es[k])]
PSnap(s) == [index |-> s.index,term |-> s.term,config |-> PCfg(s.config)]
PMsg(m) == [type |-> m.type,fromId |-> m.from,to |-> m.to,term |-> m.term,
 index |-> m.index,logTerm |-> m.logTerm,commit |-> m.commit,reject |-> m.reject,
 hint |-> m.hint,context |-> m.context,forced |-> m.forced,entries |-> PEnts(m.entries),snapshot |-> PSnap(m.snapshot)]
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
 preVote |-> r.preVote,checkQuorum |-> r.checkQuorum,isLearner |-> r.id\in r.config.learners,
 votes |-> {[id |-> n,yes |-> n\in r.yes]:n\in r.yes\cup r.no},
 storage |-> [log |-> PEnts(Suffix(r.store.hist,r.store.cut+1)),snapshot |-> PSnap(r.store.snapshot),
 hs |-> r.store.hs,cut |-> r.store.cut]]
PReady(b) == [hs |-> IF b.hasHS THEN b.hs ELSE EmptyHS,
 ss |-> IF b.hasSS THEN b.ss ELSE "__null__", entries |-> PEnts(b.entries),
 committed |-> PEnts(b.committed),messages |-> PMsgs(b.messages),reads |-> PReads(b.reads),
 snapshot |-> PSnap(b.snapshot),mustSync |-> b.mustSync,cursor |-> b.cursor]
RestartBefore(c) == [storage |-> [log |-> IF c.action="construct" THEN PEnts(Ents(c.input.entries)) ELSE <<>>,snapshot |-> PSnap(Snap(c.input.snapshot)),
 hs |-> IF c.action="construct" THEN EmptyHS ELSE [term |-> 3,vote |-> 0,commit |-> c.input.snapshot.index],cut |-> c.input.snapshot.index],
 constructor |-> [id |-> 1,applied |-> 0,electionTick |-> ElectionTick,heartbeatTick |-> HeartbeatTick,
 maxSizePerMsg |-> MaxMsgSize,maxCommittedSizePerReady |-> MaxReadySize,
 maxUncommittedEntriesSize |-> MaxUncommitted,maxInflightMsgs |-> MaxInflight]]
LocalInit == /\ selected\in Cases /\ phase=(IF IsAdvance(selected) THEN -2 ELSE IF selected.action="bootstrap_ready" THEN -3 ELSE 0)
 /\ captured=EmptyReady
 /\ raft=[n\in Server |-> IF n=1 THEN (IF IsBoot(selected) THEN InitialRaft(1,10) ELSE Built(selected)) ELSE InitialRaft(n,10)]
 /\ before=(IF IsConstruct(selected) THEN RestartBefore(selected) ELSE PState(IF IsBoot(selected) THEN InitialRaft(1,10) ELSE Built(selected)))
 /\ disk=[n\in Server |-> IF n=1 /\ IsConstruct(selected) THEN
       [EmptyDisk EXCEPT !.snapshot=Snap(selected.input.snapshot),
        !.log=IF selected.action="construct" THEN [k \in DOMAIN selected.input.entries |-> Ent(selected.input.entries[k])] ELSE EmptyFunction,
        !.hs=IF selected.action="construct" THEN EmptyHS ELSE [term |-> 3,vote |-> 0,commit |-> selected.input.snapshot.index]] ELSE EmptyDisk]
 /\ ready=[n\in Server |-> EmptyReady]
 /\ application=[n\in Server |-> IF n=1 /\ selected.action="callback_node" THEN
      [EmptyApp EXCEPT !.hist=Prefix(Ents(selected.pre.log),1),
       !.jobs= <<[batch |-> 1,snapshot |-> EmptySnapshot,entries |-> <<Ent(selected.input.entry)>>]>>] ELSE EmptyApp]
 /\ requests=[id\in RequestId |-> IF selected.action="callback_node" THEN
      [EmptyRequest EXCEPT !.status="Invoked",!.node=1,!.weight=0,!.encoded=6] ELSE EmptyRequest]
 /\ wire=EmptyBag /\ history=EmptyHistory /\ quality=EmptyQuality
Core(c,r) == CASE c.action\in {"vote","receive"} -> Step(r,Msg(c.input.message),10)
 [] c.action="proposal" -> Step(r,[Message("MsgProp",1,1,0) EXCEPT !.entries=Ents(c.input.entries)],10)
 [] c.action="propose_then_apply" ->
      LET a==Step(r,[Message("MsgProp",1,1,0) EXCEPT !.entries=Ents(c.input.entries)],10)
          e==Hist(a)[Last(a)]
      IN IF a.fatal#"" \/ a.decision#"Accepted" \/ e.kind\notin ConfKinds THEN a ELSE ApplyConfCore(a,e,10)
 [] c.action="apply" -> ApplyConfCore(r,Ent(c.input.entry),10)
 [] c.action="hup" -> Step(r,Message("MsgHup",1,1,0),10)
 [] c.action="read" -> Step(r,[Message("MsgReadIndex",1,1,0) EXCEPT !.context=c.input.context],10)
 [] c.action="readack" -> Step(r,[Message("MsgHeartbeatResp",c.input.fromId,1,0) EXCEPT !.context=c.input.context],10)
 [] c.action="checkquorum" -> Step(r,Message("MsgCheckQuorum",1,1,0),10)
 [] c.action="restore" -> Restore(r,Snap(c.input.snapshot),10)
 [] IsConstruct(c) -> RestartCore(1,10)
 [] c.action="bootstrap" -> BootState(c)
 [] c.action="bootstrap_hup" -> Step(BootState(c),Message("MsgHup",1,1,0),10)
 [] c.action="apply_then_step" -> LET a==ApplyConfCore(r,Ent(c.input.entry),10) IN
      IF a.fatal#"" THEN a ELSE Step(a,Msg(c.input.message),10)
\* Setup uses the actual original Ready action, then original Step calls.
\* Caller persistence flags and storage installation are environment mappings.
PrepareReady == /\ phase=-2 /\ ProtocolReady(1) /\ phase'=-1
 /\ captured'=ready'[1] /\ before'=PState(raft'[1])
 /\ UNCHANGED <<selected,quality>>
PrepareAdvance == /\ phase=-1 /\ phase'=0
 /\ LET r==raft[1] b==captured
         st==IF b.snapshot.index>0 THEN Store(b.snapshot.hist,b.snapshot,b.snapshot.index,r.store.hs) ELSE r.store
         persisted==StoreAppend(st,b.entries)
         a==Between([r EXCEPT !.store=[persisted EXCEPT !.hs=IF b.hasHS THEN b.hs ELSE @]],selected.input.between)
    IN /\ raft'=[raft EXCEPT ![1]=a] /\ before'=PState(a)
 /\ ready'=[ready EXCEPT ![1].done=Parts(captured),![1].installed=Parts(captured),
              ![1].published=TRUE,![1].queued=TRUE]
 /\ UNCHANGED <<selected,captured,disk,application,requests,wire,history,quality>>
Execute == /\ phase=0 /\ phase'=(IF selected.action="callback_node" THEN 2 ELSE 1) /\ UNCHANGED <<selected,before,captured,quality>>
 /\ \E c \in Cases:
   /\ selected=c
   /\ CASE c.action\in {"ready_raw","ready_node","bootstrap_ready"} -> ProtocolReady(1)
      [] IsAdvance(c) -> ProtocolAdvance(1)
      [] c.action="callback_node" -> ProtocolApplyEntry(1,10)
      [] OTHER -> /\ raft'=[raft EXCEPT ![1]=Core(c,@)]
                  /\ UNCHANGED <<disk,ready,application,requests,wire,history>>
PrepareBoot == /\ phase=-3 /\ phase'=0
 /\ \E c \in Cases:selected=c /\ raft'=[raft EXCEPT ![1]=BootState(c)]
 /\ UNCHANGED <<selected,before,captured,quality,disk,ready,application,requests,wire,history>>
CallbackPropose == /\ phase=2 /\ phase'=1
 /\ (IF raft[1].propcEnabled THEN ProtocolPropose(1,7,10) ELSE UNCHANGED protocolVars)
 /\ UNCHANGED <<selected,before,captured,quality>>
LocalNext == PrepareBoot \/ PrepareReady \/ PrepareAdvance \/ Execute \/ CallbackPropose
Result(c,r) == [state |-> PState(r),
 status |-> IF r.fatal#"" THEN "panic" ELSE IF c.action="callback_node" /\ ~r.propcEnabled THEN "disabled" ELSE IF c.action\in {"proposal","apply_then_step","callback_node","propose_then_apply"} /\ r.decision\in {"DropQuota","DropTransfer","DropRemoved","DropNoLeader","DropForwardDisabled"} THEN "dropped" ELSE "ok",
 return |-> IF r.fatal#"" THEN "__null__" ELSE
 CASE c.action\in {"apply","callback_node"} -> PCfg(r.config)
 [] c.action\in {"ready_raw","ready_node","bootstrap_ready"} -> PReady(ready[1])
 [] c.action="restore" -> [restored |-> r.usnap.index=selected.input.snapshot.index /\ r.usnap.index>0]
 [] IsAdvance(c) -> [batchAfter |-> PReady(captured)]
 [] OTHER -> "__null__"]
PInput(c) == [entries |-> PEnts(Ents(c.input.entries)),entry |-> PEnt(Ent(c.input.entry)),
 snapshot |-> PSnap(Snap(c.input.snapshot)),fromId |-> c.input.fromId,context |-> c.input.context,
 message |-> PMsg(Msg(c.input.message)),
 between |-> [k\in DOMAIN c.input.between |-> PMsg(Msg(c.input.between[k]))]]
ActualInput(c) == IF IsAdvance(c) THEN PInput(c) @@ [batch |-> PReady(IF phase=-2 THEN NewReady(raft[1]) ELSE captured)] ELSE PInput(c)
WriteResult(value) == Serialize(<<value>>, OutputDir \o "/transitions.ndjson",
 [format |-> "NDJSON",openOptions |-> <<"CREATE","APPEND">>,charset |-> "UTF-8"])
Emit == IF phase=1 THEN WriteResult(
 [protocol |-> "action-validation/v1",id |-> selected.id,engine |-> "tlc",adapter_status |-> "ok",
 testcase |-> selected,pre_observation |-> before,
 input_observation |-> ActualInput(selected),observation |-> Result(selected,raft[1]),raw_fatal |-> raft[1].fatal,
 model_witnesses |-> [coreDecision |-> raft[1].decision,autoLeaveChecks |-> history.autoLeaveChecks,
 proposal |-> IF selected.action\in {"proposal","propose_then_apply"} THEN
     ProposalObservation(Built(selected),Ents(selected.input.entries),raft[1],requests) ELSE "__null__"]]) ELSE
 IF phase\in {-3,-2,0} THEN JsonSerialize(OutputDir \o "/candidate-" \o selected.id \o ".json",
 [testcase |-> selected,pre_observation |-> before,input_observation |-> ActualInput(selected),
 setup_phase |-> IF phase=-2 THEN "Ready prerequisite" ELSE "tested action"]) ELSE TRUE
=============================================================================
