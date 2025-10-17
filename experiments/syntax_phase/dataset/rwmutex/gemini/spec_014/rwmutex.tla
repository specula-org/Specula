---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

ASSUME Threads \subseteq {"t1", "t2", "t3"}

\* Bitmask constants based on a 64-bit architecture
WRITER             == 2^(64-1)
UPGRADEABLE_READER == 2^(64-2)
BEING_UPGRADED     == 2^(64-3)
READER             == 1

\* The set of possible states for each thread
ThreadStates == {"idle", "reading", "writing", "upreading", "upgrading"}
LockTypes    == {"Read", "Write", "UpRead"}

vars == <<lock, pc, wait_queue, wants>>

lock \in Nat
pc \in [Threads -> ThreadStates]
wait_queue \in Seq(Threads)
wants \in [Threads -> LockTypes]

\* Helper operators to inspect the lock state
IsWriter(l)    == (l \div WRITER) % 2 = 1
IsUpReader(l)  == (l \div UPGRADEABLE_READER) % 2 = 1
IsUpgrading(l) == (l \div BEING_UPGRADED) % 2 = 1
ReaderCount(l) == l % UPGRADEABLE_READER

\* A thread is waiting if it's in the wait queue
IsWaiting(t) == \E i \in DOMAIN wait_queue : wait_queue[i] = t

TypeOK ==
    /\ lock \in Nat
    /\ pc \in [Threads -> ThreadStates]
    /\ wait_queue \in Seq(Threads)
    /\ wants \in [Threads -> LockTypes]
    /\ \A i \in DOMAIN wait_queue : wait_queue[i] \in Threads
    /\ \A t \in Threads : pc[t] # "idle" => ~IsWaiting(t)

Init ==
    /\ lock = 0
    /\ pc = [t \in Threads |-> "idle"]
    /\ wait_queue = <<>>
    /\ wants = [t \in Threads |-> "Read"] \* Default value, doesn't matter

\* A thread attempts to acquire a read lock.
\* If it fails, it is enqueued to wait. This models `queue.wait_until(|| self.try_read())`.
AcquireRead(t) ==
    /\ pc[t] = "idle"
    /\ ~IsWaiting(t)
    /\ IF ~IsWriter(lock) /\ ~IsUpgrading(lock)
       THEN /\ lock' = lock + READER
            /\ pc' = [pc EXCEPT ![t] = "reading"]
            /\ UNCHANGED <<wait_queue, wants>>
       ELSE /\ wait_queue' = Append(wait_queue, t)
            /\ wants' = [wants EXCEPT ![t] = "Read"]
            /\ UNCHANGED <<lock, pc>>

\* A thread releases a read lock.
\* If it was the last reader, it wakes one waiting thread.
ReleaseRead(t) ==
    /\ pc[t] = "reading"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ LET new_lock = lock - READER IN
       /\ lock' = new_lock
       /\ IF ReaderCount(lock) = 1 /\ Len(wait_queue) > 0
          THEN /\ wait_queue' = Tail(wait_queue)
          ELSE /\ UNCHANGED wait_queue
    /\ UNCHANGED wants

\* A thread attempts to acquire a write lock.
\* If it fails, it is enqueued to wait.
AcquireWrite(t) ==
    /\ pc[t] = "idle"
    /\ ~IsWaiting(t)
    /\ IF lock = 0
       THEN /\ lock' = WRITER
            /\ pc' = [pc EXCEPT ![t] = "writing"]
            /\ UNCHANGED <<wait_queue, wants>>
       ELSE /\ wait_queue' = Append(wait_queue, t)
            /\ wants' = [wants EXCEPT ![t] = "Write"]
            /\ UNCHANGED <<lock, pc>>

\* A thread releases a write lock.
\* All waiting threads are woken up.
ReleaseWrite(t) ==
    /\ pc[t] = "writing"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock' = lock - WRITER
    /\ wait_queue' = <<>>
    /\ UNCHANGED wants

\* A thread attempts to acquire an upgradeable read lock.
\* If it fails, it is enqueued to wait.
AcquireUpRead(t) ==
    /\ pc[t] = "idle"
    /\ ~IsWaiting(t)
    /\ IF ~IsWriter(lock) /\ ~IsUpReader(lock)
       THEN /\ lock' = lock + UPGRADEABLE_READER
            /\ pc' = [pc EXCEPT ![t] = "upreading"]
            /\ UNCHANGED <<wait_queue, wants>>
       ELSE /\ wait_queue' = Append(wait_queue, t)
            /\ wants' = [wants EXCEPT ![t] = "UpRead"]
            /\ UNCHANGED <<lock, pc>>

\* A thread releases an upgradeable read lock.
\* If the lock becomes empty, all waiting threads are woken up.
ReleaseUpRead(t) ==
    /\ pc[t] = "upreading"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ LET new_lock = lock - UPGRADEABLE_READER IN
       /\ lock' = new_lock
       /\ IF new_lock = 0
          THEN /\ wait_queue' = <<>>
          ELSE /\ UNCHANGED wait_queue
    /\ UNCHANGED wants

\* An upgradeable reader starts the upgrade process.
\* This sets the BEING_UPGRADED flag, which blocks new readers.
StartUpgrade(t) ==
    /\ pc[t] = "upreading"
    /\ pc' = [pc EXCEPT ![t] = "upgrading"]
    /\ lock' = lock + BEING_UPGRADED
    /\ UNCHANGED <<wait_queue, wants>>

\* An upgradeable reader completes the upgrade.
\* This can only happen when there are no other readers.
\* The state transitions atomically to a writer state.
FinishUpgrade(t) ==
    /\ pc[t] = "upgrading"
    /\ ReaderCount(lock) = 0
    /\ pc' = [pc EXCEPT ![t] = "writing"]
    /\ lock' = WRITER
    /\ UNCHANGED <<wait_queue, wants>>

\* A writer downgrades to an upgradeable reader.
\* This is assumed to always succeed when the lock is held by a writer.
Downgrade(t) ==
    /\ pc[t] = "writing"
    /\ lock = WRITER
    /\ pc' = [pc EXCEPT ![t] = "upreading"]
    /\ lock' = UPGRADEABLE_READER
    /\ UNCHANGED <<wait_queue, wants>>

\* A woken thread (one that is no longer in the wait_queue but still has pc="idle")
\* retries its acquisition. This is modeled by the main Acquire* actions.
\* This action models a waiting thread being woken and retrying its original request.
RetryAcquire(t) ==
    /\ pc[t] = "idle"
    /\ IsWaiting(t)
    /\ LET type = wants[t] IN
       /\ IF type = "Read" /\ ~IsWriter(lock) /\ ~IsUpgrading(lock)
          THEN /\ lock' = lock + READER
               /\ pc' = [pc EXCEPT ![t] = "reading"]
               /\ wait_queue' = SubSeq(wait_queue, 1, Len(wait_queue)) \o SelectSeq(wait_queue, \x -> x # t)
               /\ UNCHANGED wants
          ELSE IF type = "Write" /\ lock = 0
               THEN /\ lock' = WRITER
                    /\ pc' = [pc EXCEPT ![t] = "writing"]
                    /\ wait_queue' = SubSeq(wait_queue, 1, Len(wait_queue)) \o SelectSeq(wait_queue, \x -> x # t)
                    /\ UNCHANGED wants
               ELSE IF type = "UpRead" /\ ~IsWriter(lock) /\ ~IsUpReader(lock)
                    THEN /\ lock' = lock + UPGRADEABLE_READER
                         /\ pc' = [pc EXCEPT ![t] = "upreading"]
                         /\ wait_queue' = SubSeq(wait_queue, 1, Len(wait_queue)) \o SelectSeq(wait_queue, \x -> x # t)
                         /\ UNCHANGED wants
                    ELSE /\ UNCHANGED vars

Next ==
    \E t \in Threads:
        \/ AcquireRead(t)
        \/ AcquireWrite(t)
        \/ AcquireUpRead(t)
        \/ ReleaseRead(t)
        \/ ReleaseWrite(t)
        \/ ReleaseUpRead(t)
        \/ StartUpgrade(t)
        \/ FinishUpgrade(t)
        \/ Downgrade(t)
        \/ RetryAcquire(t)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A t \in Threads : WF_vars(AcquireRead(t) \/ AcquireWrite(t) \/ AcquireUpRead(t) \/ RetryAcquire(t))
    /\ \A t \in Threads : WF_vars(ReleaseRead(t))
    /\ \A t \in Threads : WF_vars(ReleaseWrite(t))
    /\ \A t \in Threads : WF_vars(ReleaseUpRead(t))
    /\ \A t \in Threads : WF_vars(StartUpgrade(t))
    /\ \A t \in Threads : WF_vars(FinishUpgrade(t))
    /\ \A t \in Threads : WF_vars(Downgrade(t))

====