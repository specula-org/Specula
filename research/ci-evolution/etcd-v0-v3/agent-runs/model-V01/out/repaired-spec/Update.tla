------------------------------ MODULE Update ------------------------------
EXTENDS MC

(***************************************************************************
Incremental view for source revision 16c5274b589aa75c634a1a5f2b05cf66aaf37dcc.
Reference behavior remains single-owned by base/MC; this module selects the
updated paths and their unchanged producers/consumers without copying bodies.
No EnvUpdate is used: update properties are checked over full MCNext first,
and the concrete focused view only narrows scheduling for additional depth.
***************************************************************************)

Framed(a) == a /\ UNCHANGED faultVars

\* U1/U2: ConfChangeV2 proposal and application.
\* reference: base!ProtocolInvokeV2, base!ProtocolPropose, base!ProtocolApplyEntry
\* code: rawnode.go:94-107; node.go:428-442,502-512; raft.go:999-1030,1440-1507
AffectedConfigurationActions ==
    \/ \E n\in Server,id\in RequestId,changes\in V2Batches,
          transition\in {"Auto","JointImplicit","JointExplicit"},
          w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup{0}:
          MCInvokeV2(n,id,changes,transition,w,z,parent)
    \/ \E n\in Server,id\in RequestId,t\in Timeouts:
          Framed(Original!Propose(n,id,t))
    \/ \E n\in Server,t\in Timeouts:Framed(Original!ApplyEntry(n,t))

\* U2/U3: joint quorums are consumed by campaign, receive, reads, commit,
\* CheckQuorum, and the automatic leave appended by Advance.
\* reference: base!Campaign, base!Receive, base!Advance
\* code: raft.go:554-599,766-818,971-1219; tracker/tracker.go:144-187
AffectedQuorumAndAdvanceActions ==
    \/ \E n\in Server,t\in Timeouts:MCCampaign(n,t) \/ MCTick(n,t)
    \/ \E m\in DOMAIN wire,t\in Timeouts:Framed(Original!Receive(m,t))
    \/ \E n\in Server:Framed(Original!Ready(n)) \/ Framed(Original!Advance(n))

\* U4/U5: construction and snapshot restore are changed consumers of ConfState.
\* reference: base!Restart, base!Receive(MsgSnap), base!CreateSnapshot
\* code: raft.go:321-382,1361-1430; rawnode.go:40-58; storage.go:188-210
AffectedRecoveryActions ==
    \/ \E n\in Server,t\in Timeouts:Framed(Original!Restart(n,t))
    \/ \E n\in Server:\E k\in 1..Last(raft[n]):MCCreateSnapshot(n,k)

AffectedActions ==
    \/ AffectedConfigurationActions
    \/ AffectedQuorumAndAdvanceActions
    \/ AffectedRecoveryActions

\* Concrete unchanged boundary: persist/install/publish/queue/application makes
\* configuration entries and snapshots observable; crash and delivery connect
\* recovery to the changed constructors. All bodies are the full reference actions.
InteractionActions ==
    \/ \E n\in Server:Framed(Original!Publish(n)) \/ Framed(Original!QueueApplication(n))
          \/ Framed(Original!StorageApplySnapshot(n)) \/ Framed(Original!StorageAppend(n))
          \/ Framed(Original!StorageSetHardState(n)) \/ Framed(Original!ApplySnapshot(n))
          \/ Framed(Original!FinishApplication(n)) \/ Framed(Original!SaveApplication(n))
          \/ Framed(Original!PersistLocalSnapshot(n))
    \/ \E n\in Server,part\in {"All","Entries","HS","Snapshot"}:
          Framed(Original!StartPersist(n,part)) \/ Framed(Original!CompletePersist(n,part))
    \/ \E n\in Server:MCCrash(n)
    \/ \E n\in Server:\E k\in 1..Last(raft[n]):MCCompact(n,k)
    \/ \E n\in Server,id\in RequestId:Framed(Original!CompleteWrite(n,id))
    \/ \E id\in RequestId:Framed(Original!ReturnAPI(id))

FullUpdateNext == MCNext
ConcreteUpdateNext == AffectedActions \/ InteractionActions
FullUpdateSpec == MCInit /\ [][FullUpdateNext]_mcvars
ConcreteUpdateSpec == MCInit /\ [][ConcreteUpdateNext]_mcvars

\* U1-U5 update contracts are owned by this checking view. Their reusable
\* source-state predicates live in base so Trace can evaluate the same meaning.
UpdateReadyOwnership == ReadyOwnership
UpdateAutoLeaveAdvance == AutoLeaveAdvance
UpdateJointConfigurationShape == JointConfigurationShape
UpdateJointSnapshotRecovery == JointSnapshotRecovery

\* Scenario reachability canaries are deliberately negated invariants. Their
\* dedicated cfgs succeed only by producing a violation/witness.
JointNotReached == ~\E n\in Server:raft[n].config.outgoing#{}
AutoLeaveNotAppended == ~\E n\in Server:\E e\in SeqSet(Hist(raft[n])):
    e.kind="V2" /\ e.id=0 /\ e.changes= <<>>
JointRecoveryNotReached == ~\E n\in Server:
    raft[n].alive /\ ConfigOf(raft[n].cfgHist).outgoing#{} /\
    raft[n].config#ConfigOf(raft[n].cfgHist)

=============================================================================
