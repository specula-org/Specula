---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES lock_state, pc

vars == <<lock_state, pc>>

Init ==
    /\ lock_state = [writer |-> FALSE, upgradable |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ pc = [t \in Threads |-> "idle"]

RequestRead(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "waiting_read"]
    /\ UNCHANGED <<lock_state>>

AcquireRead(t) ==
    /\ pc[t] = "waiting_read"
    /\ \lnot lock_state.writer
    /\ \lnot lock_state.upgrading
    /\ pc' = [pc EXCEPT ![t] = "reading"]
    /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]

ReleaseRead(t) ==
    /\ pc[t] = "reading"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock_state' = [lock_state EXCEPT !.readers = @ - 1]

RequestWrite(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "waiting_write"]
    /\ UNCHANGED <<lock_state>>

AcquireWrite(t) ==
    /\ pc[t] = "waiting_write"
    /\ lock_state.readers = 0
    /\ \lnot lock_state.writer
    /\ \lnot lock_state.upgradable
    /\ pc' = [pc EXCEPT ![t] = "writing"]
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]

ReleaseWrite(t) ==
    /\ pc[t] = "writing"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]

RequestUpRead(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "waiting_upread"]
    /\ UNCHANGED <<lock_state>>

AcquireUpRead(t) ==
    /\ pc[t] = "waiting_upread"
    /\ \lnot lock_state.writer
    /\ \lnot lock_state.upgradable
    /\ pc' = [pc EXCEPT ![t] = "upreading"]
    /\ lock_state' = [lock_state EXCEPT !.upgradable = TRUE]

ReleaseUpRead(t) ==
    /\ pc[t] = "upreading"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock_state' = [lock_state EXCEPT !.upgradable = FALSE]

RequestUpgrade(t) ==
    /\ pc[t] = "upreading"
    /\ pc' = [pc EXCEPT ![t] = "upgrading"]
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]

CompleteUpgrade(t) ==
    /\ pc[t] = "upgrading"
    /\ lock_state.readers = 0
    /\ pc' = [pc EXCEPT ![t] = "writing"]
    /\ lock_state' = [writer     |-> TRUE,
                      upgradable |-> FALSE,
                      upgrading  |-> FALSE,
                      readers    |-> lock_state.readers]

Downgrade(t) ==
    /\ pc[t] = "writing"
    /\ pc' = [pc EXCEPT ![t] = "upreading"]
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upgradable = TRUE]

Next ==
    \E t \in Threads:
        \/ RequestRead(t)
        \/ AcquireRead(t)
        \/ ReleaseRead(t)
        \/ RequestWrite(t)
        \/ AcquireWrite(t)
        \/ ReleaseWrite(t)
        \/ RequestUpRead(t)
        \/ AcquireUpRead(t)
        \/ ReleaseUpRead(t)
        \/ RequestUpgrade(t)
        \/ CompleteUpgrade(t)
        \/ Downgrade(t)

Spec == Init /\ [][Next]_vars /\
    (\A t \in Threads:
        /\ WF_vars(AcquireRead(t))
        /\ WF_vars(ReleaseRead(t))
        /\ WF_vars(AcquireWrite(t))
        /\ WF_vars(ReleaseWrite(t))
        /\ WF_vars(AcquireUpRead(t))
        /\ WF_vars(ReleaseUpRead(t))
        /\ WF_vars(RequestUpgrade(t))
        /\ WF_vars(CompleteUpgrade(t))
        /\ WF_vars(Downgrade(t)))

====