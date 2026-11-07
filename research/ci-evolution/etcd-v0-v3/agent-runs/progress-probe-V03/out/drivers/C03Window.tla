------------------------------ MODULE C03Window ------------------------------
EXTENDS C03Progress
\* Focus injection on the handoff window before the original leader's first
\* automatic proposal. Every placement in this window is explored.
WindowHandoff == Handoff /\ ~proposed
WindowNext == Replay \/ Pump \/ WindowHandoff \/ Early
WindowSpec == DriverInit /\ [][WindowNext]_cvars /\ WF_cvars(Replay) /\ WF_cvars(Pump)
=============================================================================
