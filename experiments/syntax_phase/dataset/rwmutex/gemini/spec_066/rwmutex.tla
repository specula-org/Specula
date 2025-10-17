---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

\* Bitmask constants based on a 64-bit architecture
WRITER             == 2^63
UPGRADEABLE_READER == 2^62
BEING_UPGRADED     == 2^61
READER             == 1

\* Helper for bitwise operations
B(n, i) == (n \div (2^i)) % 2

BITAND(n1, n2) ==
    CHOOSE r \in Nat: \A i \in 0..63: B(r, i) = IF B(n1, i) = 1 /\ B(n2, i) = 1 THEN 1 ELSE 0
BITOR(n1, n2) ==
    CHOOSE r \in Nat: \A i \in 0..63: B(r, i) = IF B(n1, i) = 1 \/ B(n2, i) = 1 THEN 1 ELSE 0
BITNOT(n) ==
    CHOOSE r \in Nat: \A i \in 0..63: B(r, i) = 1 - B(n, i)

\* State extraction helpers
HasWriter(l)          == BITAND(l, WRITER) /= 0
HasUpReader(l)        == BITAND(l, UPGRADEABLE_READER) /= 0
IsBeingUpgraded(l)    == BITAND(l, BEING_UPGRADED) /= 0
ReaderCount(l)        == BITAND(l, BEING_UPGRADED - 1)

VARIABLES lock, pc, waitQueue

vars == <<lock, pc, waitQueue>>

PCStates == {"idle", "wants_read", "reading", "wants_write", "writing",
             "wants_upread", "upreading", "upgrading"}

TypeOK ==
    /\ lock \in Nat
    /\ pc \in [Threads -> PCStates]
    /\ waitQueue \in Seq(Threads)
    /\ \A i \in DOMAIN waitQueue: waitQueue[i] \in Threads

Init ==
    /\ lock = 0
    /\ pc = [p \in Threads |-> "idle"]
    /\ waitQueue = << >>

\* A thread decides it wants to acquire a lock
Request(p) ==
    /\ pc[p] = "idle"
    /\ \/ pc' = [pc EXCEPT ![p] = "wants_read"]
       \/ pc' = [pc EXCEPT ![p] = "wants_write"]
       \/ pc' = [pc EXCEPT ![p] = "wants_upread"]
    /\ UNCHANGED <<lock, waitQueue>>

\* A thread tries to acquire a read lock. It either succeeds or blocks.
TryRead(p) ==
    /\ pc[p] = "wants_read"
    /\ \lnot (p \in AsSet(waitQueue))
    /\ IF BITAND(lock, BITOR(WRITER, BEING_UPGRADED)) = 0 THEN
        /\ lock' = lock + READER
        /\ pc' = [pc EXCEPT ![p] = "reading"]
        /\ UNCHANGED <<waitQueue>>
       ELSE
        /\ waitQueue' = Append(waitQueue, p)
        /\ UNCHANGED <<lock, pc>>

\* A thread tries to acquire a write lock. It either succeeds or blocks.
TryWrite(p) ==
    /\ pc[p] = "wants_write"
    /\ \lnot (p \in AsSet(waitQueue))
    /\ IF lock = 0 THEN
        /\ lock' = WRITER
        /\ pc' = [pc EXCEPT ![p] = "writing"]
        /\ UNCHANGED <<waitQueue>>
       ELSE
        /\ waitQueue' = Append(waitQueue, p)
        /\ UNCHANGED <<lock, pc>>

\* A thread tries to acquire an upgradeable read lock. It either succeeds or blocks.
TryUpRead(p) ==
    /\ pc[p] = "wants_upread"
    /\ \lnot (p \in AsSet(waitQueue))
    /\ IF BITAND(lock, BITOR(WRITER, UPGRADEABLE_READER)) = 0 THEN
        /\ lock' = BITOR(lock, UPGRADEABLE_READER)
        /\ pc' = [pc EXCEPT ![p] = "upreading"]
        /\ UNCHANGED <<waitQueue>>
       ELSE
        /\ waitQueue' = Append(waitQueue, p)
        /\ UNCHANGED <<lock, pc>>

\* A thread releases a read lock. If it's the last reader, it wakes one waiter.
ReleaseRead(p) ==
    /\ pc[p] = "reading"
    /\ lock' = lock - READER
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ waitQueue' = IF ReaderCount(lock) = 1 /\ Len(waitQueue) > 0
                    THEN Tail(waitQueue)
                    ELSE waitQueue

\* A thread releases a write lock. It wakes all waiters.
ReleaseWrite(p) ==
    /\ pc[p] = "writing"
    /\ lock' = BITAND(lock, BITNOT(WRITER))
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ waitQueue' = << >>

\* A thread releases an upgradeable read lock. It may wake all waiters.
ReleaseUpRead(p) ==
    /\ pc[p] = "upreading"
    /\ lock' = lock - UPGRADEABLE_READER
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ waitQueue' = IF lock = UPGRADEABLE_READER
                    THEN << >>
                    ELSE waitQueue

\* An upgradeable reader starts the upgrade process.
StartUpgrade(p) ==
    /\ pc[p] = "upreading"
    /\ lock' = BITOR(lock, BEING_UPGRADED)
    /\ pc' = [pc EXCEPT ![p] = "upgrading"]
    /\ UNCHANGED <<waitQueue>>

\* An upgradeable reader completes the upgrade once all other readers are gone.
CompleteUpgrade(p) ==
    /\ pc[p] = "upgrading"
    /\ ReaderCount(lock) = 0
    /\ lock' = WRITER
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ UNCHANGED <<waitQueue>>

\* A writer downgrades its lock to an upgradeable read lock.
Downgrade(p) ==
    /\ pc[p] = "writing"
    /\ lock' = UPGRADEABLE_READER
    /\ pc' = [pc EXCEPT ![p] = "upreading"]
    /\ UNCHANGED <<waitQueue>>

Next ==
    \E p \in Threads:
        \/ Request(p)
        \/ TryRead(p)
        \/ TryWrite(p)
        \/ TryUpRead(p)
        \/ ReleaseRead(p)
        \/ ReleaseWrite(p)
        \/ ReleaseUpRead(p)
        \/ StartUpgrade(p)
        \/ CompleteUpgrade(p)
        \/ Downgrade(p)

Fairness ==
    /\ \A p \in Threads: WF_vars(Request(p))
    /\ \A p \in Threads: WF_vars(TryRead(p))
    /\ \A p \in Threads: WF_vars(TryWrite(p))
    /\ \A p \in Threads: WF_vars(TryUpRead(p))
    /\ \A p \in Threads: WF_vars(ReleaseRead(p))
    /\ \A p \in Threads: WF_vars(ReleaseWrite(p))
    /\ \A p \in Threads: WF_vars(ReleaseUpRead(p))
    /\ \A p \in Threads: WF_vars(StartUpgrade(p))
    /\ \A p \in Threads: WF_vars(CompleteUpgrade(p))
    /\ \A p \in Threads: WF_vars(Downgrade(p))

Spec == Init /\ [][Next]_vars /\ Fairness

====