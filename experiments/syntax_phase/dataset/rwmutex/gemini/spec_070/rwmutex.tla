---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    \* The set of processes
    Proc,

    \* Bitmask for a single reader
    READER,

    \* Bitmask for the "being upgraded" state
    BEING_UPGRADED,

    \* Bitmask for an upgradeable reader
    UPGRADEABLE_READER,

    \* Bitmask for a writer
    WRITER

ASSUME
    /\ READER = 1
    /\ BEING_UPGRADED = 256
    /\ UPGRADEABLE_READER = 512
    /\ WRITER = 1024
    /\ Proc = {"p1", "p2"}

VARIABLES
    \* The state of the lock, represented as a bitfield
    lock,

    \* The program counter for each process
    pc,

    \* The FIFO queue of waiting processes
    wait_queue

vars == <<lock, pc, wait_queue>>

IsWriterLocked(l) == (l \div WRITER) % 2 = 1
IsUpReaderLocked(l) == (l \div UPGRADEABLE_READER) % 2 = 1
IsBeingUpgraded(l) == (l \div BEING_UPGRADED) % 2 = 1
ReaderCount(l) == l % BEING_UPGRADED
IsBlocked(p) == \E i \in 1..Len(wait_queue): wait_queue[i] = p

TypeOK ==
    /\ lock \in Nat
    /\ pc \in [Proc -> {"idle", "wants_read", "reading", "wants_write", "writing",
                        "wants_upread", "upreading", "upgrading"}]
    /\ wait_queue \in Seq(Proc)

Init ==
    /\ lock = 0
    /\ pc = [p \in Proc |-> "idle"]
    /\ wait_queue = << >>

\* A process decides it wants to acquire a read lock.
RequestRead(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "wants_read"]
    /\ UNCHANGED <<lock, wait_queue>>

\* A process decides it wants to acquire a write lock.
RequestWrite(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "wants_write"]
    /\ UNCHANGED <<lock, wait_queue>>

\* A process decides it wants to acquire an upgradeable read lock.
RequestUpRead(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "wants_upread"]
    /\ UNCHANGED <<lock, wait_queue>>

\* A process that is not blocked attempts to acquire a lock.
\* It either succeeds and changes state, or fails and gets enqueued.
AcquireOrBlock(p) ==
    /\ \lnot IsBlocked(p)
    /\ CASE pc[p] = "wants_read" ->
        /\ IF \lnot IsWriterLocked(lock) /\ \lnot IsBeingUpgraded(lock) THEN
            \* Acquire read lock successfully
            /\ lock' = lock + READER
            /\ pc' = [pc EXCEPT ![p] = "reading"]
            /\ UNCHANGED wait_queue
        ELSE
            \* Block
            /\ wait_queue' = Append(wait_queue, p)
            /\ UNCHANGED <<lock, pc>>
    [] pc[p] = "wants_write" ->
        /\ IF lock = 0 THEN
            \* Acquire write lock successfully
            /\ lock' = WRITER
            /\ pc' = [pc EXCEPT ![p] = "writing"]
            /\ UNCHANGED wait_queue
        ELSE
            \* Block
            /\ wait_queue' = Append(wait_queue, p)
            /\ UNCHANGED <<lock, pc>>
    [] pc[p] = "wants_upread" ->
        /\ IF \lnot IsWriterLocked(lock) /\ \lnot IsUpReaderLocked(lock) THEN
            \* Acquire upgradeable read lock successfully
            /\ lock' = lock + UPGRADEABLE_READER
            /\ pc' = [pc EXCEPT ![p] = "upreading"]
            /\ UNCHANGED wait_queue
        ELSE
            \* Block
            /\ wait_queue' = Append(wait_queue, p)
            /\ UNCHANGED <<lock, pc>>

\* A process releases its read lock.
ReleaseRead(p) ==
    /\ pc[p] = "reading"
    /\ LET old_lock == lock IN
       /\ lock' = lock - READER
       /\ pc' = [pc EXCEPT ![p] = "idle"]
       /\ IF old_lock = READER /\ Len(wait_queue) > 0 THEN
            \* Last reader releases, wake one waiter.
            /\ wait_queue' = Tail(wait_queue)
       ELSE
            /\ UNCHANGED wait_queue

\* A process releases its write lock.
ReleaseWrite(p) ==
    /\ pc[p] = "writing"
    /\ lock' = lock - WRITER
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ wait_queue' = << >>  \* Wake all waiters

\* A process releases its upgradeable read lock.
ReleaseUpRead(p) ==
    /\ pc[p] = "upreading"
    /\ LET old_lock == lock IN
       /\ lock' = lock - UPGRADEABLE_READER
       /\ pc' = [pc EXCEPT ![p] = "idle"]
       /\ IF old_lock = UPGRADEABLE_READER THEN
            \* Lock becomes free, wake all waiters.
            /\ wait_queue' = << >>
       ELSE
            /\ UNCHANGED wait_queue

\* An upgradeable reader starts the upgrade process.
StartUpgrade(p) ==
    /\ pc[p] = "upreading"
    /\ lock' = lock + BEING_UPGRADED
    /\ pc' = [pc EXCEPT ![p] = "upgrading"]
    /\ UNCHANGED wait_queue

\* An upgrade attempt completes successfully.
\* This can only happen when there are no other readers.
CompleteUpgrade(p) ==
    /\ pc[p] = "upgrading"
    /\ lock = UPGRADEABLE_READER + BEING_UPGRADED
    /\ lock' = WRITER
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ UNCHANGED wait_queue

\* A writer downgrades its lock to an upgradeable read lock.
Downgrade(p) ==
    /\ pc[p] = "writing"
    /\ lock = WRITER
    /\ lock' = UPGRADEABLE_READER
    /\ pc' = [pc EXCEPT ![p] = "upreading"]
    /\ UNCHANGED wait_queue

ProcActions(p) ==
    \/ RequestRead(p)
    \/ RequestWrite(p)
    \/ RequestUpRead(p)
    \/ AcquireOrBlock(p)
    \/ ReleaseRead(p)
    \/ ReleaseWrite(p)
    \/ ReleaseUpRead(p)
    \/ StartUpgrade(p)
    \/ CompleteUpgrade(p)
    \/ Downgrade(p)

Next ==
    \E p \in Proc: ProcActions(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Proc : WF_vars(ProcActions(p))

====