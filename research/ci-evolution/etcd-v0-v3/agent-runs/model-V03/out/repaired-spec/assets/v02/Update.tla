------------------------------ MODULE Update ------------------------------
EXTENDS MC

(***************************************************************************
Incremental view for source revision 3d0faba4ee302b1b61b3eaa084fafc284854ac07
(protocol files aligned with 46580dcf61734b12ae757dbabdf31c2b862acd68).
Reference behavior remains single-owned by base/MC. This module selects the
changed V02 paths and their unchanged producers/consumers without copying any
implementation semantics. FullUpdateSpec is authoritative; the concrete view
only provides a deeper schedule lens, so no EnvUpdate or discharge claim is
made.
***************************************************************************)

Framed(a) == a /\ UNCHANGED faultVars

\* V02-U1: learner vote requests now follow the ordinary vote/log-freshness
\* path, while learner campaigns remain rejected.
\* reference: base!StepVote, base!StepHup, base!ProtocolReceive
\* code: raft.go:899-972,1456-1460
AffectedElectionActions ==
    \/ \E n\in Server,t\in Timeouts:MCCampaign(n,t) \/ MCTick(n,t)
    \/ \E m\in DOMAIN wire,t\in Timeouts:
         /\ m.type\in {"MsgVote","MsgPreVote","MsgVoteResp","MsgPreVoteResp"}
         /\ Framed(Original!Receive(m,t))

\* V02-U2: public RawNode.Ready and delivered Node Ready now both accept
\* SoftState/messages/read states; Advance preserves later output.
\* reference: base!ProtocolReady, base!ProtocolAdvance
\* code: rawnode.go:119-177; node.go:306-320,385-390
AffectedReadyActions ==
    \E n\in Server:Framed(Original!Ready(n)) \/ Framed(Original!Advance(n))

\* V02-U3: construction and a successful live snapshot restore reconstruct all
\* ConfState fields. The unchanged pre-restore membership guard remains in focus.
\* reference: base!Restart, base!Restore, base!ProtocolReceive
\* code: confchange/restore.go:22-154; raft.go:322-367,1381-1453
AffectedRecoveryActions ==
    \/ \E n\in Server,t\in Timeouts:Framed(Original!Restart(n,t))
    \/ \E m\in DOMAIN wire,t\in Timeouts:
         /\ m.type="MsgSnap"
         /\ Framed(Original!Receive(m,t))

\* Existing configuration transitions create the joint states consumed by all
\* three changed mechanisms.
\* reference: base!ProtocolInvokeV2, base!ProtocolPropose, base!ProtocolApplyEntry
\* code: raft.go:999-1030,1463-1532; confchange/confchange.go:35-357
AffectedConfigurationActions ==
    \/ \E n\in Server,id\in RequestId,changes\in V2Batches,
          transition\in {"Auto","JointImplicit","JointExplicit"},
          w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup{0}:
          MCInvokeV2(n,id,changes,transition,w,z,parent)
    \/ \E n\in Server,id\in RequestId,t\in Timeouts:
          Framed(Original!Propose(n,id,t))
    \/ \E n\in Server,t\in Timeouts:Framed(Original!ApplyEntry(n,t))

AffectedActions ==
    \/ AffectedElectionActions
    \/ AffectedReadyActions
    \/ AffectedRecoveryActions
    \/ AffectedConfigurationActions

\* Concrete old context persists, publishes, applies, snapshots and crashes the
\* state crossing the changed boundaries. Full MCNext remains the completeness
\* guard for all other actions and properties.
InteractionActions ==
    \/ \E n\in Server:Framed(Original!Publish(n)) \/ Framed(Original!QueueApplication(n))
          \/ Framed(Original!StorageApplySnapshot(n)) \/ Framed(Original!StorageAppend(n))
          \/ Framed(Original!StorageSetHardState(n)) \/ Framed(Original!ApplySnapshot(n))
          \/ Framed(Original!FinishApplication(n)) \/ Framed(Original!SaveApplication(n))
          \/ Framed(Original!PersistLocalSnapshot(n))
    \/ \E n\in Server,part\in {"All","Entries","HS","Snapshot"}:
          Framed(Original!StartPersist(n,part)) \/ Framed(Original!CompletePersist(n,part))
    \/ \E n\in Server:MCCrash(n)
    \/ \E n\in Server:\E k\in 1..Last(raft[n]):MCCreateSnapshot(n,k) \/ MCCompact(n,k)
    \/ \E n\in Server,id\in RequestId:Framed(Original!CompleteWrite(n,id))
    \/ \E id\in RequestId:Framed(Original!ReturnAPI(id))
    \/ \E m\in DOMAIN wire,t\in Timeouts:Framed(Original!Receive(m,t))

FullUpdateNext == MCNext
ConcreteUpdateNext == AffectedActions \/ InteractionActions
FullUpdateSpec == MCInit /\ [][FullUpdateNext]_mcvars
ConcreteUpdateSpec == MCInit /\ [][ConcreteUpdateNext]_mcvars

\* V02-U1: source-permitted learner grants satisfy the same term/vote/log
\* contract; campaign and decision-side quorum eligibility remain constrained.
UpdateLearnerVoteContract == VoteDecisionEligibility
UpdateLearnerCampaignEligibility == LearnerEligibility
\* V02-U2: acceptance occurs at Ready and later output survives Advance.
UpdateReadyOwnership == ReadyOwnership
UpdateAdvanceOutputPreservation == AckPreservation
\* V02-U3: full configurations survive accepted live restore and restart.
UpdateJointConfigurationShape == JointConfigurationShape
UpdateJointSnapshotRecovery == JointSnapshotRecovery
\* V02-U4: outgoing-only joint members must not be stranded by the unchanged
\* incoming/current-learner precheck (raft.go:1398-1420).
UpdateJointSnapshotMemberAcceptance == JointSnapshotMemberAcceptance
\* Retained interaction guards.
UpdateAutoLeaveAdvance == AutoLeaveAdvance
UpdateQuorumAccounting == QuorumAccounting

\* Reachability canaries are deliberately negated invariants. Dedicated hunt
\* configurations use their violations only as evidence that the mechanism ran.
LearnerGrantNotReached == ~\E x\in history.grants:x.learner
PostReadyOutputNotReached == ~\E a\in history.acks:a.outBefore#EmptyBag \/ a.readsBefore# <<>>
OutgoingSnapshotRestoreNotReached == ~\E x\in history.restoreChecks:
    x.fresh /\ x.follower /\ x.fullMember /\ ~x.sourceMember /\ ~x.matches
JointRecoveryNotReached == ~\E x\in history.recovery:
    x.expectedConfig.outgoing#{} /\ x.config=x.expectedConfig
JointNotReached == ~\E n\in Server:raft[n].config.outgoing#{}
AutoLeaveNotAppended == ~\E n\in Server:\E e\in SeqSet(Hist(raft[n])):
    e.kind="V2" /\ e.id=0 /\ e.changes= <<>>

=============================================================================
