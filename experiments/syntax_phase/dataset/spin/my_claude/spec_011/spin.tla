---- MODULE spin ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES 
    lock_state,
    holder,
    pc,
    guards

Vars == <<lock_state, holder, pc, guards>>

TypeOK ==
    /\ lock_state \in BOOLEAN
    /\ holder \in Threads \cup {NULL}
    /\ pc \in [Threads -> {"idle", "trying", "spinning", "locked"}]
    /\ guards \in [Threads -> BOOLEAN]

Init ==
    /\ lock_state = FALSE
    /\ holder = NULL
    /\ pc = [t \in Threads |-> "idle"]
    /\ guards = [t \in Threads |-> FALSE]

TryLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "trying"]
    /\ guards' = [guards EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<lock_state, holder>>

CompareExchangeSuccess(t) ==
    /\ pc[t] = "trying"
    /\ lock_state = FALSE
    /\ lock_state' = TRUE
    /\ holder' = t
    /\ pc' = [pc EXCEPT ![t] = "locked"]
    /\ UNCHANGED guards

CompareExchangeFail(t) ==
    /\ pc[t] = "trying"
    /\ lock_state = TRUE
    /\ pc' = [pc EXCEPT ![t] = "spinning"]
    /\ UNCHANGED <<lock_state, holder, guards>>

SpinLoop(t) ==
    /\ pc[t] = "spinning"
    /\ lock_state = TRUE
    /\ pc' = [pc EXCEPT ![t] = "trying"]
    /\ UNCHANGED <<lock_state, holder, guards>>

AcquireLock(t) ==
    \/ CompareExchangeSuccess(t)
    \/ CompareExchangeFail(t)

SpinWait(t) ==
    SpinLoop(t)

TryLockImmediate(t) ==
    /\ pc[t] = "idle"
    /\ guards' = [guards EXCEPT ![t] = TRUE]
    /\ IF lock_state = FALSE
       THEN /\ lock_state' = TRUE
            /\ holder' = t
            /\ pc' = [pc EXCEPT ![t] = "locked"]
       ELSE /\ pc' = [pc EXCEPT ![t] = "idle"]
            /\ guards' = [guards EXCEPT ![t] = FALSE]
            /\ UNCHANGED <<lock_state, holder>>

Unlock(t) ==
    /\ pc[t] = "locked"
    /\ holder = t
    /\ lock_state' = FALSE
    /\ holder' = NULL
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ guards' = [guards EXCEPT ![t] = FALSE]

Next ==
    \E t \in Threads :
        \/ TryLock(t)
        \/ AcquireLock(t)
        \/ SpinWait(t)
        \/ TryLockImmediate(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====