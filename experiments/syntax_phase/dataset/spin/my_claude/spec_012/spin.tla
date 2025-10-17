---- MODULE spin ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES 
    lock_state,
    holder,
    pc

Vars == <<lock_state, holder, pc>>

TypeOK == 
    /\ lock_state \in BOOLEAN
    /\ holder \in Threads \cup {NULL}
    /\ pc \in [Threads -> {"idle", "trying", "spinning", "locked"}]

Init ==
    /\ lock_state = FALSE
    /\ holder = NULL
    /\ pc = [t \in Threads |-> "idle"]

TryLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, holder>>

CompareExchangeSuccess(t) ==
    /\ pc[t] = "trying"
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ holder' = t
    /\ pc' = [pc EXCEPT ![t] = "locked"]

CompareExchangeFail(t) ==
    /\ pc[t] = "trying"
    /\ lock_state = TRUE
    /\ pc' = [pc EXCEPT ![t] = "spinning"]
    /\ UNCHANGED <<lock_state, holder>>

SpinLoop(t) ==
    /\ pc[t] = "spinning"
    /\ lock_state = TRUE
    /\ pc' = [pc EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, holder>>

Unlock(t) ==
    /\ pc[t] = "locked"
    /\ holder = t
    /\ lock_state' = FALSE
    /\ holder' = NULL
    /\ pc' = [pc EXCEPT ![t] = "idle"]

Next ==
    \E t \in Threads :
        \/ TryLock(t)
        \/ CompareExchangeSuccess(t)
        \/ CompareExchangeFail(t)
        \/ SpinLoop(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====