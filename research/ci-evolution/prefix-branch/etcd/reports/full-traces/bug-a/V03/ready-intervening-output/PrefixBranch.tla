------------------------------ MODULE PrefixBranch ------------------------------
EXTENDS Trace, Update, TLC
CONSTANTS PBPoints, PBMaxSteps, PBAfter
VARIABLES pbAt, pbStep, pbBranched, pbSlot, pbAction
pbVars == <<vars, l, faultCount, pbAt, pbStep, pbBranched, pbSlot, pbAction>>
PBInit == MCInit /\ l = 2 /\ pbAt \in PBPoints /\ pbStep = 0 /\ pbBranched = FALSE /\ pbSlot = 1 /\ pbAction = 0
PBReplay == /\ ~pbBranched /\ pbStep < pbAt /\ l <= Len(TraceLog) /\ MatchEvent(logline)
    /\ l' = l + 1 /\ pbStep' = pbStep + 1 /\ UNCHANGED <<faultCount, pbAt, pbBranched, pbSlot, pbAction>>
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
    /\ pbStep' = pbStep + 1 /\ UNCHANGED <<l, faultCount, pbAt, pbBranched, pbAction>>
PBProbe1 ==
    \E n\in Server,t\in Timeouts:MCCampaign(n,t)
PBProbe2 ==
    \E n\in Server,t\in Timeouts:MCTick(n,t)
PBProbe3 ==
    \E m\in DOMAIN wire,t\in Timeouts:
         /\ m.type\in {"MsgVote","MsgPreVote","MsgVoteResp","MsgPreVoteResp"}
         /\ Framed(Original!Receive(m,t))
PBProbe4 ==
    \E n\in Server:Framed(Original!Ready(n))
PBProbe5 ==
    \E n\in Server:Framed(Original!Advance(n))
PBProbe6 ==
    \E n\in Server,t\in Timeouts:Framed(Original!Restart(n,t))
PBProbe7 ==
    \E m\in DOMAIN wire,t\in Timeouts:
         /\ m.type="MsgSnap"
         /\ Framed(Original!Receive(m,t))
PBProbe8 ==
    \E n\in Server,id\in RequestId,kind\in WorkloadKinds\{"Read","V2"},
          target\in Server\cup{0},w\in PayloadWeights,z\in EncodedWeights,
          parent\in RequestId\cup{0}:
          \E ctx\in {id,0}:MCInvoke(n,id,kind,target,w,z,parent,ctx)
PBProbe9 ==
    \E n\in Server,id\in RequestId,changes\in V2Batches,
          transition\in {"Auto","JointImplicit","JointExplicit"},
          w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup{0}:
          MCInvokeV2(n,id,changes,transition,w,z,parent)
PBProbe10 ==
    \E n\in Server,id\in RequestId,t\in Timeouts:
          Framed(Original!Propose(n,id,t))
PBProbe11 ==
    \E n\in Server,t\in Timeouts:Framed(Original!ApplyEntry(n,t))
PBProbe12 ==
    \E n,p\in Server,t\in Timeouts:MCTransfer(n,p,t)
PBProbe13 ==
    \E m\in DOMAIN wire,t\in Timeouts:
         /\ m.type\in {"MsgApp","MsgAppResp","MsgHeartbeat","MsgHeartbeatResp", "MsgTimeoutNow"}
         /\ Framed(Original!Receive(m,t))
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
       \/ PBProbe11 /\ pbAction' = 11
       \/ PBProbe12 /\ pbAction' = 12
       \/ PBProbe13 /\ pbAction' = 13
    /\ pbBranched' = TRUE /\ pbStep' = pbStep + 1 /\ UNCHANGED <<l, pbAt, pbSlot>>
PBSpec == PBInit /\ [][PBReplay \/ PBSettle \/ PBBranch]_pbVars
PBReplayed == l <= Len(TraceLog)
PBAllPoints == 0..(PBMaxSteps - 1)
PBConstraint == ~pbBranched \/ (StateConstraint)
PB_CampaignDecisionEligibility == ~pbBranched \/ CampaignDecisionEligibility
=============================================================================
