------------------------------ MODULE C03Controls ------------------------------
EXTENDS C03Clocked
NoExplicitJoint == ~\E n\in Server:raft[n].config.outgoing#{} /\ ~raft[n].config.autoLeave
NormalCrossingEffect == \A a\in history.autoLeaveChecks:
    a.crossingEligible => /\ a.appended
        /\ LET e==a.afterHist[Len(a.afterHist)] IN IsLeave(e) /\ e.weight=0
=============================================================================
