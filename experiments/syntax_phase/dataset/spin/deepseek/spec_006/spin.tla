
---- MODULE spin ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads
Null == CHOOSE n : n \notin Threads

VARIABLES lock, holder, trying

TypeOK == 
    lock \in BOOLEAN
    /\ holder \in Threads \cup {Null}
    /\ trying \subseteq Threads
    /\ (lock = (holder # Null))

Init == 
    lock = FALSE
    /\ holder = Null
    /\ trying = {}

StartLock(t) == 
    /\ t \in Threads
    /\ trying' = trying \cup {t}
    /\ UNCHANGED <<lock, holder>>

LockAcquire(t) == 
    /\ t \in trying
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ holder' = t
    /\ trying' = trying \ {t}

LockSpin(t) == 
    /\ t \in trying
    /\ lock = TRUE
    /\ UNCHANGED <<lock, holder, trying>>

TryLockSucceed(t) == 
    /\ t \in Threads
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ holder' = t
    /\ UNCHANGED <<trying>>

TryLockFail(t) == 
    /\ t \in Threads
    /\ lock = TRUE
    /\ UNCHANGED <<lock, holder, trying>>

Unlock(t) == 
    /\ t \in Threads
    /\ holder = t
    /\ lock = TRUE
    /\ lock' = FALSE
    /\ holder' = Null
    /\ UNCHANGED <<trying>>

Next == 
    \E t \in Threads :
        StartLock(t) \/ LockAcquire(t) \/ LockSpin(t) \/ 
        TryLockSucceed(t) \/ TryLockFail(t) \/ Unlock(t)

ThreadAction(t) == 
    StartLock(t) \/ LockAcquire(t) \/ LockSpin(t) \/ 
    TryLockSucceed(t) \/ TryLockFail(t) \/ Unlock(t)

Spec == 
    Init 
    /\ [][Next]_<<lock, holder, trying>>
    /\ \A t \in Threads : WF_<<lock, holder, trying>>(ThreadAction(t))
    /\ \A t \in Threads : SF_<<lock, holder, trying>>(LockAcquire(t))
====