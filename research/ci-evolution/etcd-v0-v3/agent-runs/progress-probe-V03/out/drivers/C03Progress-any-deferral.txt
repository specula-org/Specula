---------------------------- MODULE C03Progress ----------------------------
EXTENDS Trace
CONSTANTS PrefixEnd, AllowHandoff, AllowEarly, NodeAPI, SerialNetwork
VARIABLES slot, transferUsed, earlyUsed, deferNode, barrier, installed, proposed, completed, lastEvent
cvars == <<traceVars,slot,transferUsed,earlyUsed,deferNode,barrier,installed,proposed,completed,lastEvent>>
DriverRawNodes == IF NodeAPI THEN {} ELSE TraceRawNodes
EpisodeIndex == 5
EpisodeInstalled(n) == Len(raft[n].cfgHist)>=EpisodeIndex /\
    raft[n].cfgHist[EpisodeIndex].id=1 /\ raft[n].config.outgoing#{} /\ raft[n].config.autoLeave
RetainedExit(n) == \E e\in SeqSet(Hist(raft[n])):e.index>EpisodeIndex /\ IsLeave(e)
AppliedExit(n) == \E e\in SeqSet(application[n].hist):e.index>EpisodeIndex /\ IsLeave(e)
Eligible(n) ==
    /\ EpisodeInstalled(n) /\ raft[n].role="Leader"
    /\ n\in VoterIDs(raft[n].config)
    /\ raft[n].applied>=Max(EpisodeIndex,barrier[n])
    /\ ~RetainedExit(n)
    /\ ~\E e\in SeqSet(Hist(raft[n])):e.kind\in ConfKinds /\ e.index>raft[n].applied
Settled == \A n\in {1,2,4}:AppliedExit(n) /\ raft[n].config.outgoing={} /\ ~raft[n].config.autoLeave
Healthy == \A n\in Server:Live(n) /\ raft[n].snapAvailable
Stable(n) == <>[](Healthy /\ raft[n].role="Leader" /\ n\in VoterIDs(raft[n].config))
ProposalProgress == \A n\in Server:Stable(n) => (Eligible(n) ~> RetainedExit(n))
CompletionProgress == \A n\in Server:Stable(n) => (EpisodeInstalled(n) ~> Settled)
PrefixApplicable == l>PrefixEnd \/ ENABLED MatchEvent(TraceLog[l])
NoFatal == \A n\in Server:raft[n].fatal=""
NoEligible == ~\E n\in Server:Eligible(n)
NoEarly == ~earlyUsed
NoInstalled == installed={}
NoProposal == ~proposed
NoCompletion == ~completed
NoTransferEligibility == ~(transferUsed /\ Eligible(2))
NoDeferredEligibility == ~(earlyUsed /\ Eligible(1))
NoRetainedDeferredExit == ~\E n\in Server:RetainedExit(n) /\ ~AppliedExit(n) /\
    \E e\in SeqSet(Hist(raft[n])):e.index>EpisodeIndex /\ IsLeave(e) /\ raft[n].applied>=e.index
Monitors ==
    /\ deferNode'=IF deferNode=0 THEN 0 ELSE IF ready'[deferNode].active THEN deferNode ELSE 0
    /\ barrier'=[n\in Server |-> IF raft'[n].role="Leader" /\ raft[n].role#"Leader"
                                THEN Last(raft[n]) ELSE barrier[n]]
    /\ installed'=installed\cup {n\in Server:EpisodeInstalled(n)'}
    /\ proposed'=(proposed \/ (\E n\in Server:RetainedExit(n)'))
    /\ completed'=(completed \/ Settled')
DriverInit ==
    /\ Init /\ l=2 /\ slot=1 /\ transferUsed=FALSE /\ earlyUsed=FALSE
    /\ deferNode=0 /\ barrier=[n\in Server |-> 0] /\ installed={} /\ proposed=FALSE /\ completed=FALSE
    /\ lastEvent=[action |-> "Init",node |-> 0]
Replay ==
    /\ l<=PrefixEnd /\ MatchEvent(TraceLog[l]) /\ l'=l+1
    /\ Monitors /\ lastEvent'=[action |-> TraceLog[l].event,node |-> 0]
    /\ UNCHANGED <<slot,transferUsed,earlyUsed>>
Services == <<"Ready","StartPersist","CompletePersist","StorageApplySnapshot",
    "StorageAppend","StorageSetHardState","Publish","QueueApplication",
    "ApplyEntry","FinishApplication","Advance","Receive","ReturnAPI","Tick">>
Nodes == <<1,2,3,4>>
Slots == Len(Services)*Len(Nodes)
NodeAt(k) == Nodes[((k-1)%Len(Nodes))+1]
ServiceAt(k) == Services[((k-1)\div Len(Nodes))+1]
Drained ==
    /\ wire=EmptyBag
    /\ \A n\in Server:~ready[n].active /\ raft[n].out=EmptyBag /\
         application[n].jobs= <<>> /\ ~ContainsUpdates(NewReady(raft[n]))
Delivery(n) == IF SerialNetwork THEN
    LET ms=={m\in DOMAIN wire:m.to=n} IN
      /\ ms#{} /\ Receive(CHOOSE m\in ms:TRUE,raft[n].timeout)
    ELSE \E m\in DOMAIN wire:m.to=n /\ Receive(m,raft[n].timeout)
Publication(n) ==
    /\ Publish(n)
    /\ IF ~SerialNetwork \/ ready[n].remainingMessages=EmptyBag THEN TRUE ELSE
        wire'=AddBag(wire,CHOOSE m\in DOMAIN ready[n].remainingMessages:TRUE)
Service(n,s) ==
    CASE s="Ready" -> /\ ContainsUpdates(NewReady(raft[n])) /\ Ready(n)
      [] s="StartPersist" -> StartPersist(n,"All")
      [] s="CompletePersist" -> CompletePersist(n,"All")
      [] s="StorageApplySnapshot" -> StorageApplySnapshot(n)
      [] s="StorageAppend" -> StorageAppend(n)
      [] s="StorageSetHardState" -> StorageSetHardState(n)
      [] s="Publish" -> Publication(n)
      [] s="QueueApplication" -> QueueApplication(n)
      [] s="ApplyEntry" -> /\ deferNode#n /\ ApplyEntry(n,raft[n].timeout)
      [] s="FinishApplication" -> /\ deferNode#n /\ FinishApplication(n)
      [] s="Advance" -> /\ (application[n].jobs= <<>> \/ deferNode=n) /\ Advance(n)
      [] s="Receive" -> Delivery(n)
      [] s="ReturnAPI" -> n=1 /\ ReturnAPI(1)
      [] OTHER -> /\ Drained /\ raft[n].role="Leader" /\ Tick(n,raft[n].timeout)
\* Skip disabled service slots in the scheduler only. Each enabled transition
\* still calls exactly one reference action; handoff/early choices remain
\* available between every pair of reference actions.
OffsetSlot(d) == ((slot-1+d)%Slots)+1
EnabledOffsets == {d\in 0..(Slots-1):
    ENABLED Service(NodeAt(OffsetSlot(d)),ServiceAt(OffsetSlot(d)))}
Pump ==
    /\ l>PrefixEnd /\ EnabledOffsets#{}
    /\ LET k==OffsetSlot(MinSet(EnabledOffsets)) n==NodeAt(k) s==ServiceAt(k) IN
       /\ Service(n,s) /\ Monitors /\ lastEvent'=[action |-> s,node |-> n]
       /\ slot'=(k%Slots)+1
    /\ UNCHANGED <<l,transferUsed,earlyUsed>>
Handoff ==
    /\ l>PrefixEnd /\ AllowHandoff /\ ~transferUsed /\ raft[1].role="Leader"
    /\ TransferLeader(1,2,raft[1].timeout) /\ Monitors
    /\ transferUsed'=TRUE /\ lastEvent'=[action |-> "TransferLeader",node |-> 1]
    /\ UNCHANGED <<l,slot,earlyUsed>>
\* Choosing deferred application is a caller scheduling decision, hence a
\* stuttering step of the reference. The pump then fairly publishes/persists,
\* calls the original Advance when legal, and resumes ordered application.
Early ==
    /\ l>PrefixEnd /\ AllowEarly /\ ~earlyUsed
    /\ \E n\in Server:
       /\ application[n].jobs# <<>> /\ ready[n].active
       /\ deferNode'=n /\ lastEvent'=[action |-> "DeferApplication",node |-> n]
    /\ earlyUsed'=TRUE
    /\ UNCHANGED <<vars,l,slot,transferUsed,barrier,installed,proposed,completed>>
DriverNext == Replay \/ Pump \/ Handoff \/ Early
DriverSpec == DriverInit /\ [][DriverNext]_cvars /\ WF_cvars(Replay) /\ WF_cvars(Pump)
\* Only identity fields are quotiented. No protocol, history, budget or monitor
\* field is removed. No action/property reads these identities except to copy.
IdentityView == <<
    [n\in Server |-> [raft[n] EXCEPT !.readySeq=0]], disk,
    [n\in Server |-> [ready[n] EXCEPT !.id=0]],
    [n\in Server |-> [application[n] EXCEPT !.jobs=
       [k\in DOMAIN @ |-> [@[k] EXCEPT !.batch=0]]]],
    requests,wire,history,quality,l,slot,transferUsed,earlyUsed,deferNode,barrier,installed,proposed,completed,lastEvent>>
=============================================================================
