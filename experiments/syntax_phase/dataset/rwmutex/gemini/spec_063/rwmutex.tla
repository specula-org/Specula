---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

ASSUME Threads = {"t1", "t2"}

\* Bitmask constants representing the lock state
CONSTANTS
    READER_UNIT,
    BEING_UPGRADED_FLAG,
    UP_READER_FLAG,
    WRITER_FLAG

ASSUME
    /\ READER_UNIT = 1
    /\ BEING_UPGRADED_FLAG = 2^29
    /\ UP_READER_FLAG = 2^30
    /\ WRITER_FLAG = 2^31

VARIABLES lock, pc, wait_queue, woken

vars == <<lock, pc, wait_queue, woken>>

PCStates == {"idle", "reading", "writing", "up_reading", "upgrading",
             "wait_read", "wait_write", "wait_upread"}

TypeOK ==
    /\ lock \in Nat
    /\ pc \in [Threads -> PCStates]
    /\ wait_queue \in Seq(Threads)
    /\ woken \in SUBSET Threads

\* Helper operators to interpret the lock state
Readers(l) == l % BEING_UPGRADED_FLAG
IsWriter(l) == (l \land WRITER_FLAG) # 0
IsUpReader(l) == (l \land UP_READER_FLAG) # 0
IsUpgrading(l) == (l \land BEING_UPGRADED_FLAG) # 0

\* Helper to remove an element from a sequence
Remove(seq, elem) == SubSeq(seq, {i \in 1..Len(seq) : seq[i] # elem})

Init ==
    /\ lock = 0
    /\ pc = [p \in Threads |-> "idle"]
    /\ wait_queue = <<>>
    /\ woken = {}

\* A thread tries to acquire a read lock.
\* It succeeds if there is no writer and no one upgrading.
\* Otherwise, it blocks and enqueues itself.
AcquireRead(p) ==
    /\ pc[p] = "idle"
    /\ \lnot IsWriter(lock) /\ \lnot IsUpgrading(lock)
    /\ lock' = lock + READER_UNIT
    /\ pc' = [pc EXCEPT ![p] = "reading"]
    /\ UNCHANGED <<wait_queue, woken>>

BlockForRead(p) ==
    /\ pc[p] = "idle"
    /\ (IsWriter(lock) \/ IsUpgrading(lock))
    /\ pc' = [pc EXCEPT ![p] = "wait_read"]
    /\ wait_queue' = Append(wait_queue, p)
    /\ UNCHANGED <<lock, woken>>

\* A thread tries to acquire a write lock.
\* It succeeds only if the lock is completely free.
\* Otherwise, it blocks and enqueues itself.
AcquireWrite(p) ==
    /\ pc[p] = "idle"
    /\ lock = 0
    /\ lock' = WRITER_FLAG
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ UNCHANGED <<wait_queue, woken>>

BlockForWrite(p) ==
    /\ pc[p] = "idle"
    /\ lock # 0
    /\ pc' = [pc EXCEPT ![p] = "wait_write"]
    /\ wait_queue' = Append(wait_queue, p)
    /\ UNCHANGED <<lock, woken>>

\* A thread tries to acquire an upgradeable read lock.
\* It succeeds if there is no writer and no other upgradeable reader.
\* Otherwise, it blocks and enqueues itself.
AcquireUpRead(p) ==
    /\ pc[p] = "idle"
    /\ \lnot IsWriter(lock) /\ \lnot IsUpReader(lock)
    /\ lock' = lock \lor UP_READER_FLAG
    /\ pc' = [pc EXCEPT ![p] = "up_reading"]
    /\ UNCHANGED <<wait_queue, woken>>

BlockForUpRead(p) ==
    /\ pc[p] = "idle"
    /\ (IsWriter(lock) \/ IsUpReader(lock))
    /\ pc' = [pc EXCEPT ![p] = "wait_upread"]
    /\ wait_queue' = Append(wait_queue, p)
    /\ UNCHANGED <<lock, woken>>

\* A woken thread retries its acquisition.
ProcessWoken(p) ==
    /\ pc[p] \in {"wait_read", "wait_write", "wait_upread"}
    /\ p \in woken
    /\ woken' = woken \ {p}
    /\ CASE pc[p] = "wait_read" /\ \lnot IsWriter(lock) /\ \lnot IsUpgrading(lock) ->
            /\ lock' = lock + READER_UNIT
            /\ pc' = [pc EXCEPT ![p] = "reading"]
            /\ wait_queue' = Remove(wait_queue, p)
       [] pc[p] = "wait_write" /\ lock = 0 ->
            /\ lock' = WRITER_FLAG
            /\ pc' = [pc EXCEPT ![p] = "writing"]
            /\ wait_queue' = Remove(wait_queue, p)
       [] pc[p] = "wait_upread" /\ \lnot IsWriter(lock) /\ \lnot IsUpReader(lock) ->
            /\ lock' = lock \lor UP_READER_FLAG
            /\ pc' = [pc EXCEPT ![p] = "up_reading"]
            /\ wait_queue' = Remove(wait_queue, p)
       [] OTHER ->
            UNCHANGED <<lock, pc, wait_queue>>

\* A reader releases its lock. If it's the last lock holder, it wakes one waiter.
ReleaseRead(p) ==
    /\ pc[p] = "reading"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ lock' = lock - READER_UNIT
    /\ IF lock = READER_UNIT /\ Len(wait_queue) > 0
       THEN woken' = woken \union {Head(wait_queue)}
       ELSE UNCHANGED woken
    /\ UNCHANGED wait_queue

\* A writer releases its lock and wakes all waiting threads.
ReleaseWrite(p) ==
    /\ pc[p] = "writing"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ lock' = 0
    /\ woken' = woken \union BagToSet(wait_queue)
    /\ UNCHANGED wait_queue

\* An upgradeable reader releases its lock. If it's the last lock holder, it wakes all.
ReleaseUpRead(p) ==
    /\ pc[p] = "up_reading"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ lock' = lock - UP_READER_FLAG
    /\ IF lock = UP_READER_FLAG /\ Len(wait_queue) > 0
       THEN woken' = woken \union BagToSet(wait_queue)
       ELSE UNCHANGED woken
    /\ UNCHANGED wait_queue

\* An upgradeable reader starts the upgrade process, blocking new readers.
StartUpgrade(p) ==
    /\ pc[p] = "up_reading"
    /\ pc' = [pc EXCEPT ![p] = "upgrading"]
    /\ lock' = lock \lor BEING_UPGRADED_FLAG
    /\ UNCHANGED <<wait_queue, woken>>

\* An upgrading thread completes the upgrade when all other readers are gone.
CompleteUpgrade(p) ==
    /\ pc[p] = "upgrading"
    /\ Readers(lock) = 0
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ lock' = WRITER_FLAG
    /\ UNCHANGED <<wait_queue, woken>>

\* A writer downgrades its lock to an upgradeable read lock.
Downgrade(p) ==
    /\ pc[p] = "writing"
    /\ lock = WRITER_FLAG
    /\ pc' = [pc EXCEPT ![p] = "up_reading"]
    /\ lock' = UP_READER_FLAG
    /\ UNCHANGED <<wait_queue, woken>>

Next ==
    \E p \in Threads:
        \/ AcquireRead(p) \/ BlockForRead(p)
        \/ AcquireWrite(p) \/ BlockForWrite(p)
        \/ AcquireUpRead(p) \/ BlockForUpRead(p)
        \/ ProcessWoken(p)
        \/ ReleaseRead(p)
        \/ ReleaseWrite(p)
        \/ ReleaseUpRead(p)
        \/ StartUpgrade(p)
        \/ CompleteUpgrade(p)
        \/ Downgrade(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
