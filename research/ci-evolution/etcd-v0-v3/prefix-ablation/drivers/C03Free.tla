------------------------------- MODULE C03Free -------------------------------
EXTENDS C03Clocked
\* The probe's driver with part of the recorded prefix left to the search.
\* Events 2..PrefixEnd are replayed as before. The client inputs recorded after
\* PrefixEnd (Campaign, InvokeV2, Propose) keep their recorded parameters, but
\* each may happen once at any point and in any order. The recorded service
\* events after PrefixEnd are not replayed: the probe's own fair pump does that
\* work. PrefixEnd = 1 starts the search at Init, and PrefixEnd = 153 is the
\* original probe. Service scheduling, the one optional leader transfer,
\* fairness and the checked properties are unchanged.
VARIABLE pending
freeVars == <<clockVars,pending>>
ClientEvents == {"Campaign","InvokeV2","Propose"}
FreeInputs == {i\in (PrefixEnd+1)..Len(TraceLog):TraceLog[i].event\in ClientEvents}
FreeInput(i) ==
    /\ l>PrefixEnd /\ i\in pending
    /\ MatchEvent(TraceLog[i]) /\ Monitors
    /\ lastEvent'=[action |-> TraceLog[i].event,node |-> 0]
    /\ pending'=pending\{i}
    /\ UNCHANGED <<l,slot,transferUsed,earlyUsed,tickPending>>
Scheduled(A) == A /\ UNCHANGED pending
FreeInit == ClockInit /\ pending=FreeInputs
FreeNext == Scheduled(ClockNext) \/ \E i\in pending:FreeInput(i)
\* No fairness on the inputs: the search decides whether and when they happen.
FreeSpec == FreeInit /\ [][FreeNext]_freeVars /\ WF_freeVars(Scheduled(ClockReplay))
    /\ WF_freeVars(Scheduled(ClockPump)) /\ WF_freeVars(Scheduled(FollowerTick))
FreeView == <<ClockView,pending>>
=============================================================================
