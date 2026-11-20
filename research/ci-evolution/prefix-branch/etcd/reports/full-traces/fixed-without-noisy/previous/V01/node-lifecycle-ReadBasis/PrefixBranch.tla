------------------------------ MODULE PrefixBranch ------------------------------
EXTENDS Trace, Update, TLC
CONSTANTS PBPoints, PBMaxSteps, PBAfter
VARIABLES pbAt, pbStep, pbBroken, pbBranched, pbSlot, pbAction
pbVars == <<vars, l, faultCount, pbAt, pbStep, pbBroken, pbBranched, pbSlot, pbAction>>
PBInit == MCInit /\ l = 2 /\ pbAt \in PBPoints /\ pbStep = 0 /\ pbBranched = FALSE /\ pbSlot = 1 /\ pbAction = 0 /\ pbBroken = {}
PBReplay == /\ ~pbBranched /\ pbStep < pbAt /\ l <= Len(TraceLog) /\ MatchEvent(logline)
    /\ l' = l + 1 /\ pbStep' = pbStep + 1 /\ UNCHANGED <<faultCount, pbAt, pbBroken, pbBranched, pbSlot, pbAction>>
PBSettle1 ==
    \E n\in Server,id\in RequestId,t\in Timeouts:Propose(n,id,t)
PBSettle2 ==
    \E n\in Server,id\in RequestId,t\in Timeouts:ReadIndex(n,id,t)
PBSettle3 ==
    \E id\in RequestId:ReturnAPI(id)
PBSettle4 ==
    \E m\in DOMAIN wire,t\in Timeouts:Receive(m,t)
PBSettle5 ==
    \E n\in Server:Ready(n) \/ Publish(n) \/ QueueApplication(n) \/ Advance(n)
             \/ StorageApplySnapshot(n) \/ StorageAppend(n) \/ StorageSetHardState(n)
             \/ ApplySnapshot(n) \/ FinishApplication(n) \/ SaveApplication(n)
             \/ PersistLocalSnapshot(n)
PBSettle6 ==
    \E n\in Server,part\in {"All","Entries","HS","Snapshot"}:StartPersist(n,part) \/ CompletePersist(n,part)
PBSettle7 ==
    \E n\in Server,t\in Timeouts:ApplyEntry(n,t) \/ Restart(n,t)
PBSettle8 ==
    \E n\in Server,id\in RequestId:CompleteWrite(n,id) \/
             (\E k\in DOMAIN application[n].reads:CompleteRead(n,id,k))
PBPart(i) == CASE i = 1 -> PBSettle1
    [] i = 2 -> PBSettle2
    [] i = 3 -> PBSettle3
    [] i = 4 -> PBSettle4
    [] i = 5 -> PBSettle5
    [] i = 6 -> PBSettle6
    [] i = 7 -> PBSettle7
    [] i = 8 -> PBSettle8
PBParts == 8
PBOffsets == {d \in 0..(PBParts - 1) : ENABLED PBPart(((pbSlot - 1 + d) % PBParts) + 1)}
PBFirst == CHOOSE d \in PBOffsets : \A e \in PBOffsets : d <= e
PBSettle == /\ IF pbBranched THEN pbStep < pbAt + 1 + PBAfter ELSE l > Len(TraceLog) /\ pbStep < pbAt
    /\ PBOffsets # {}
    /\ LET i == ((pbSlot - 1 + PBFirst) % PBParts) + 1 IN PBPart(i) /\ pbSlot' = (i % PBParts) + 1
    /\ pbStep' = pbStep + 1 /\ UNCHANGED <<l, faultCount, pbAt, pbBroken, pbBranched, pbAction>>
PBProbe1 ==
    \E n\in Server,id\in RequestId,changes\in V2Batches,
          transition\in {"Auto","JointImplicit","JointExplicit"},
          w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup{0}:
          MCInvokeV2(n,id,changes,transition,w,z,parent)
PBProbe2 ==
    \E n\in Server,id\in RequestId,t\in Timeouts:
          Framed(Original!Propose(n,id,t))
PBProbe3 ==
    \E n\in Server,t\in Timeouts:Framed(Original!ApplyEntry(n,t))
PBProbe4 ==
    \E n\in Server,t\in Timeouts:MCCampaign(n,t)
PBProbe5 ==
    \E n\in Server,t\in Timeouts:MCTick(n,t)
PBProbe6 ==
    \E m\in DOMAIN wire,t\in Timeouts:Framed(Original!Receive(m,t))
PBProbe7 ==
    \E n\in Server:Framed(Original!Ready(n))
PBProbe8 ==
    \E n\in Server:Framed(Original!Advance(n))
PBProbe9 ==
    \E n\in Server,t\in Timeouts:Framed(Original!Restart(n,t))
PBProbe10 ==
    \E n\in Server:\E k\in 1..Last(raft[n]):MCCreateSnapshot(n,k)
PBBranch == /\ ~pbBranched /\ pbStep = pbAt
    /\ \/ PBProbe1 /\ pbAction' = 1
       \/ PBProbe2 /\ pbAction' = 2
       \/ PBProbe3 /\ pbAction' = 3
       \/ PBProbe4 /\ pbAction' = 4
       \/ PBProbe5 /\ pbAction' = 5
       \/ PBProbe6 /\ pbAction' = 6
       \/ PBProbe7 /\ pbAction' = 7
       \/ PBProbe8 /\ pbAction' = 8
       \/ PBProbe9 /\ pbAction' = 9
       \/ PBProbe10 /\ pbAction' = 10
    /\ pbBroken' = (IF ReadBasis THEN {} ELSE {"ReadBasis"})
    /\ pbBranched' = TRUE /\ pbStep' = pbStep + 1 /\ UNCHANGED <<l, pbAt, pbSlot>> /\ (\A id \in RequestId : (requests[id].status = "Unused" /\ requests'[id].status = "Invoked" /\ requests'[id].kind = "V2") => ConfigWellFormed(ConfigCandidate(raft[requests'[id].node].config, [kind |-> "V2", id |-> id, changes |-> requests'[id].changes, transition |-> requests'[id].transition])))
PBSpec == PBInit /\ [][PBReplay \/ PBSettle \/ PBBranch]_pbVars
PBReplayed == l <= Len(TraceLog)
PBReplayOnly == l' = l + 1
PBAllPoints == 0..(PBMaxSteps - 1)
PBConstraint == ~pbBranched \/ (StateConstraint)
PB_ReadBasis == ~pbBranched \/ "ReadBasis" \in pbBroken \/ ReadBasis
=============================================================================
