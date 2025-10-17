---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

ASSUME Threads \subseteq {"t1", "t2", "t3"}

VARIABLES lock, pc, wait_queue, waiting_for

vars == <<lock, pc, wait_queue, waiting_for>>

\* Bitmask constants based on a 64-bit usize
WRITER             == 2^(63)
UPGRADEABLE_READER == 2^(62)
BEING_UPGRADED     == 2^(61)
READER             == 1
READER_MASK        == BEING_UPGRADED - 1

TypeOK ==
    /\ lock \in Nat
    /\ pc \in [Threads -> {"idle", "want_read", "reading", "want_write", "writing",
                           "want_upread", "upreading", "start_upgrade", "upgrading",
                           "want_downgrade", "writing_from_upgrade", "blocked"}]
    /\ wait_queue \in Seq(Threads)
    /\ waiting_for \in [Threads -> {"read", "write", "upread"}]

Init ==
    /\ lock = 0
    /\ pc = [t \in Threads |-> "idle"]
    /\ wait_queue = << >>
    /\ waiting_for = [t \in Threads |-> "read"] \* Default value, only meaningful when blocked

\*-----------------------------------------------------------------------------
\* Actions for acquiring and releasing a read lock.
\*-----------------------------------------------------------------------------
TryRead(t) ==
    /\ pc[t] = "want_read"
    /\ (lock \cap (WRITER \lor BEING_UPGRADED)) = 0
    /\ lock' = lock + READER
    /\ pc' = [pc EXCEPT ![t] = "reading"]
    /\ UNCHANGED <<wait_queue, waiting_for>>

BlockOnRead(t) ==
    /\ pc[t] = "want_read"
    /\ (lock \cap (WRITER \lor BEING_UPGRADED)) /= 0
    /\ t \notin Elems(wait_queue)
    /\ wait_queue' = Append(wait_queue, t)
    /\ pc' = [pc EXCEPT ![t] = "blocked"]
    /\ waiting_for' = [waiting_for EXCEPT ![t] = "read"]
    /\ UNCHANGED <<lock>>

ReleaseRead(t) ==
    /\ pc[t] = "reading"
    /\ LET old_lock == lock IN
       /\ lock' = old_lock - READER
       /\ IF old_lock = READER /\ Len(wait_queue) > 0 THEN
          /\ LET woken_thread == Head(wait_queue) IN
             /\ wait_queue' = Tail(wait_queue)
             /\ pc' = [pc EXCEPT ![t] = "idle", ![woken_thread] = "want_" \o waiting_for[woken_thread]]
       ELSE
          /\ wait_queue' = wait_queue
          /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<waiting_for>>

\*-----------------------------------------------------------------------------
\* Actions for acquiring and releasing a write lock.
\*-----------------------------------------------------------------------------
TryWrite(t) ==
    /\ pc[t] = "want_write"
    /\ lock = 0
    /\ lock' = WRITER
    /\ pc' = [pc EXCEPT ![t] = "writing"]
    /\ UNCHANGED <<wait_queue, waiting_for>>

BlockOnWrite(t) ==
    /\ pc[t] = "want_write"
    /\ lock /= 0
    /\ t \notin Elems(wait_queue)
    /\ wait_queue' = Append(wait_queue, t)
    /\ pc' = [pc EXCEPT ![t] = "blocked"]
    /\ waiting_for' = [waiting_for EXCEPT ![t] = "write"]
    /\ UNCHANGED <<lock>>

ReleaseWrite(t) ==
    /\ pc[t] \in {"writing", "writing_from_upgrade"}
    /\ lock' = lock - WRITER
    /\ LET woken_threads == Elems(wait_queue) IN
       /\ wait_queue' = << >>
       /\ pc' = [pc EXCEPT ![t] = "idle", ![w \in woken_threads] = "want_" \o waiting_for[w]]
    /\ UNCHANGED <<waiting_for>>

\*-----------------------------------------------------------------------------
\* Actions for acquiring and releasing an upgradeable read lock.
\*-----------------------------------------------------------------------------
TryUpread(t) ==
    /\ pc[t] = "want_upread"
    /\ (lock \cap (WRITER \lor UPGRADEABLE_READER)) = 0
    /\ lock' = lock + UPGRADEABLE_READER
    /\ pc' = [pc EXCEPT ![t] = "upreading"]
    /\ UNCHANGED <<wait_queue, waiting_for>>

BlockOnUpread(t) ==
    /\ pc[t] = "want_upread"
    /\ (lock \cap (WRITER \lor UPGRADEABLE_READER)) /= 0
    /\ t \notin Elems(wait_queue)
    /\ wait_queue' = Append(wait_queue, t)
    /\ pc' = [pc EXCEPT ![t] = "blocked"]
    /\ waiting_for' = [waiting_for EXCEPT ![t] = "upread"]
    /\ UNCHANGED <<lock>>

ReleaseUpread(t) ==
    /\ pc[t] = "upreading"
    /\ LET old_lock == lock IN
       /\ lock' = old_lock - UPGRADEABLE_READER
       /\ IF old_lock = UPGRADEABLE_READER THEN
          /\ LET woken_threads == Elems(wait_queue) IN
             /\ wait_queue' = << >>
             /\ pc' = [pc EXCEPT ![t] = "idle", ![w \in woken_threads] = "want_" \o waiting_for[w]]
       ELSE
          /\ wait_queue' = wait_queue
          /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<waiting_for>>

\*-----------------------------------------------------------------------------
\* Actions for upgrading an upread lock to a write lock.
\*-----------------------------------------------------------------------------
StartUpgrade(t) ==
    /\ pc[t] = "upreading"
    /\ lock' = lock + BEING_UPGRADED
    /\ pc' = [pc EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED <<wait_queue, waiting_for>>

\* This action models a successful attempt to upgrade. The spin-wait is modeled
\* by this action being disabled if there are any readers.
FinishUpgrade(t) ==
    /\ pc[t] = "upgrading"
    /\ lock = UPGRADEABLE_READER + BEING_UPGRADED
    /\ lock' = WRITER
    /\ pc' = [pc EXCEPT ![t] = "writing_from_upgrade"]
    /\ UNCHANGED <<wait_queue, waiting_for>>

\*-----------------------------------------------------------------------------
\* Action for downgrading a write lock to an upread lock.
\*-----------------------------------------------------------------------------
Downgrade(t) ==
    /\ pc[t] = "writing_from_upgrade"
    /\ lock = WRITER
    /\ lock' = UPGRADEABLE_READER
    /\ pc' = [pc EXCEPT ![t] = "upreading"]
    /\ UNCHANGED <<wait_queue, waiting_for>>

\*-----------------------------------------------------------------------------
\* Top-level actions initiated by threads.
\*-----------------------------------------------------------------------------
RequestRead(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "want_read"]
    /\ UNCHANGED <<lock, wait_queue, waiting_for>>

RequestWrite(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "want_write"]
    /\ UNCHANGED <<lock, wait_queue, waiting_for>>

RequestUpread(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "want_upread"]
    /\ UNCHANGED <<lock, wait_queue, waiting_for>>

\*-----------------------------------------------------------------------------
\* Definition of the next-state relation.
\*-----------------------------------------------------------------------------
Next ==
    \E t \in Threads:
        \/ RequestRead(t)
        \/ RequestWrite(t)
        \/ RequestUpread(t)
        \/ TryRead(t)
        \/ BlockOnRead(t)
        \/ ReleaseRead(t)
        \/ TryWrite(t)
        \/ BlockOnWrite(t)
        \/ ReleaseWrite(t)
        \/ TryUpread(t)
        \/ BlockOnUpread(t)
        \/ ReleaseUpread(t)
        \/ StartUpgrade(t)
        \/ FinishUpgrade(t)
        \/ Downgrade(t)

\*-----------------------------------------------------------------------------
\* Specification with fairness.
\*-----------------------------------------------------------------------------
Fairness == \A t \in Threads:
    /\ WF_vars(RequestRead(t))
    /\ WF_vars(RequestWrite(t))
    /\ WF_vars(RequestUpread(t))
    /\ WF_vars(TryRead(t))
    /\ WF_vars(BlockOnRead(t))
    /\ WF_vars(ReleaseRead(t))
    /\ WF_vars(TryWrite(t))
    /\ WF_vars(BlockOnWrite(t))
    /\ WF_vars(ReleaseWrite(t))
    /\ WF_vars(TryUpread(t))
    /\ WF_vars(BlockOnUpread(t))
    /\ WF_vars(ReleaseUpread(t))
    /\ WF_vars(StartUpgrade(t))
    /\ WF_vars(FinishUpgrade(t))
    /\ WF_vars(Downgrade(t))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================