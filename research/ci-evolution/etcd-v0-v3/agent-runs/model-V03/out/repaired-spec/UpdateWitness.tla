-------------------------- MODULE UpdateWitness --------------------------
EXTENDS Trace

(***************************************************************************
Source-backed V02 reachability checks. TraceSpec calls full base Actions and
matches every source/caller post-state; these negated invariants identify the
first exact state exhibiting each Scenario. They supplement, never replace,
the unconstrained full/focused BFS and simulations in Update.tla.
***************************************************************************)
WitnessJointNotReached == ~\E n\in Server:raft[n].config.outgoing#{}
WitnessAutoLeaveNotAppended == ~\E n\in Server:\E e\in SeqSet(Hist(raft[n])):
    e.kind="V2" /\ e.id=0 /\ e.changes= <<>>
WitnessJointRecoveryNotReached == ~\E x\in history.recovery:
    x.expectedConfig.outgoing#{} /\ x.config=x.expectedConfig
WitnessLearnerGrantNotReached == ~\E x\in history.grants:x.learner
WitnessPostReadyOutputNotReached == ~\E a\in history.acks:
    a.outBefore#EmptyBag \/ a.readsBefore# <<>>
WitnessOutgoingSnapshotRestoreNotReached == ~\E x\in history.restoreChecks:
    x.fresh /\ x.follower /\ x.fullMember /\ ~x.sourceMember /\ ~x.matches
=============================================================================
