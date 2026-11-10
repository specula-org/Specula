------------------------- MODULE QualityManagement -------------------------
EXTENDS QualityTrace
CONSTANT ManagementCuts
VARIABLES managementCut, owed, settled
managementVars == <<qualityTraceVars,managementCut,owed,settled>>
QueuedEffects(app) ==
    UNION {UNION {{[node |-> n, id |-> e.id, index |-> e.index]:
      e\in {x\in SeqSet(j.entries):x.kind\in ConfKinds /\ x.id#0}}:
      j\in SeqSet(app[n].jobs)}:n\in Server}
\* Small, explicitly seeded post-commit windows from fully validated real trace.
\* Observed source/caller state is exact; pre-window accumulated ghosts reset.
\* No claim about reaching commit or survival of future crashes is made here.
ManagementInit ==
    /\ managementCut\in ManagementCuts
    /\ LET p==Decode(TraceLog[managementCut].post) IN
       /\ raft=[n\in Server |-> Override(InitialRaft(n,p.raft[n].timeout),p.raft[n])]
       /\ disk=p.disk /\ ready=p.ready /\ application=p.application
       /\ requests=p.requests /\ wire=p.wire /\ history=EmptyHistory
       /\ owed=QueuedEffects(p.application)
    /\ settled={} /\ quality=EmptyQuality /\ l=managementCut+1
DrainEntry(n) ==
    /\ ApplyEntry(n,ElectionTick)
    /\ quality'=QualityEvent("ApplyEntry",[node |-> n])
    /\ LET e==Head(Head(application[n].jobs).entries) IN
         settled'=IF e.kind\in ConfKinds /\ e.id#0
            THEN settled\cup {[node |-> n,id |-> e.id,index |-> e.index]} ELSE settled
    /\ UNCHANGED <<l,managementCut,owed>>
DrainFinish(n) == FinishApplication(n) /\ quality'=EmptyQuality
    /\ UNCHANGED <<l,managementCut,owed,settled>>
DrainAdvance(n) == Advance(n) /\ quality'=EmptyQuality
    /\ UNCHANGED <<l,managementCut,owed,settled>>
ManagementNext == \E n\in Server:DrainEntry(n) \/ DrainFinish(n) \/ DrainAdvance(n)
ManagementFairSpec == ManagementInit /\ [][ManagementNext]_managementVars /\
    (\A n\in Server:WF_managementVars(DrainEntry(n)) /\ WF_managementVars(DrainFinish(n)))
ManagementUnfairSpec == ManagementInit /\ [][ManagementNext]_managementVars
QueuedManagementNonvacuous == owed#{}
QueuedManagementDrains == <>(owed\subseteq settled /\ \A n\in Server:application[n].jobs= <<>>)
=============================================================================
