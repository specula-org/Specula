---- MODULE SpinLock ----

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Threads

VARIABLES
    lock,
    waiting,
    pc

vars == <<lock, waiting, pc>>

Init ==
    /\ lock = FALSE
    /\ waiting = {}
    /\ pc = [t \in Threads |-> "idle"]

TryAcquire(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "trying"]
    /\ IF lock = FALSE
       THEN /\ lock' = TRUE
            /\ UNCHANGED waiting
       ELSE /\ waiting' = waiting \cup {t}
            /\ UNCHANGED lock

Release(t) ==
    /\ pc[t] = "trying"
    /\ lock = TRUE
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ IF waiting = {}
       THEN /\ lock' = FALSE
            /\ UNCHANGED waiting
       ELSE /\ \E next \in waiting:
                /\ waiting' = waiting \ {next}
                /\ UNCHANGED lock

Next ==
    \E t \in Threads:
        \/ TryAcquire(t)
        \/ Release(t)

Spec == Init /\ [][Next]_vars

====