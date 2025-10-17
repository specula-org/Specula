---- MODULE UnknownModule ----

EXTENDS Naturals, Sequences, FiniteSets

VARIABLES votedFor, grant, m

\* Original code fragment preserved exactly as given
Action ==
    /\ IF grant /\ ~m.prevote
       THEN votedFor' = [votedFor EXCEPT ![s] = m.candidateId]
       ELSE UNCHANGED votedFor

====