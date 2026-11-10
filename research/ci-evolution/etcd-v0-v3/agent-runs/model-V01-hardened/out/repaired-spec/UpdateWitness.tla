-------------------------- MODULE UpdateWitness --------------------------
EXTENDS Trace

(***************************************************************************
Source-backed U1-U5 reachability checks. TraceSpec calls full base Actions and
matches every source/caller post-state; these negated invariants identify the
first exact state exhibiting each Scenario. They supplement, never replace,
the unconstrained full/focused BFS and simulations in Update.tla.
***************************************************************************)
WitnessJointNotReached == ~\E n\in Server:raft[n].config.outgoing#{}
WitnessAutoLeaveNotAppended == ~\E n\in Server:\E e\in SeqSet(Hist(raft[n])):
    e.kind="V2" /\ e.id=0 /\ e.changes= <<>>
WitnessJointRecoveryNotReached == ~\E n\in Server:
    raft[n].alive /\ ConfigOf(raft[n].cfgHist).outgoing#{} /\
    raft[n].config#ConfigOf(raft[n].cfgHist)
=============================================================================
