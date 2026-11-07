------------------------------ MODULE C03Clocked ------------------------------
EXTENDS C03Progress
VARIABLE tickPending
clockVars == <<cvars,tickPending>>
ClockInit == DriverInit /\ tickPending={}
ClockReplay == Replay /\ UNCHANGED tickPending
ClockPump ==
    /\ tickPending={} /\ Pump
    /\ tickPending'=IF lastEvent'.action="Tick"
        THEN VoterIDs(raft'[lastEvent'.node].config)\{lastEvent'.node} ELSE {}
FollowerTick ==
    /\ tickPending#{}
    /\ LET n==MinSet(tickPending) IN
       /\ Tick(n,raft[n].timeout) /\ Monitors
       /\ lastEvent'=[action |-> "Tick",node |-> n]
       /\ tickPending'=tickPending\{n}
    /\ UNCHANGED <<l,slot,transferUsed,earlyUsed>>
ClockHandoff == Handoff /\ ~proposed /\ UNCHANGED tickPending
ClockEarly == Early /\ UNCHANGED tickPending
ClockNext == ClockReplay \/ ClockPump \/ FollowerTick \/ ClockHandoff \/ ClockEarly
ClockSpec == ClockInit /\ [][ClockNext]_clockVars /\ WF_clockVars(ClockReplay)
    /\ WF_clockVars(ClockPump) /\ WF_clockVars(FollowerTick)
ClockView == <<IdentityView,tickPending>>
=============================================================================
