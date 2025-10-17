---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Bitwise

CONSTANT Threads
ASSUME Threads = {"t1", "t2", "t3"}

(* Bitmask constants from the Rust code, scaled down for TLC *)
WRITER             == 2^31
UPGRADEABLE_READER == 2^30
BEING_UPGRADED     == 2^29
READER             == 1

(* Helper functions to decode the lock state *)
IsWriterLocked(l)    == (l \b_and WRITER) /= 0
IsUpReaderLocked(l)  == (l \b_and UPGRADEABLE_READER) /= 0
IsBeingUpgraded(l)   == (l \b_and BEING_UPGRADED) /= 0
ReaderCount(l)       == l \b_and (BEING_UPGRADED - 1)

VARIABLES
    lock,
    thread_state,
    wait_queue

vars == <<lock, thread_state, wait_queue>>

TypeOK ==
    /\ lock \in Nat
    /\ thread_state \in [Threads -> {"idle", "waiting_read", "waiting_write", "waiting_upread",
                                     "reading", "writing", "upreading", "upgrading"}]
    /\ wait_queue \in Seq(Threads)

Init ==
    /\ lock = 0
    /\ thread_state = [t \in Threads |-> "idle"]
    /\ wait_queue = <<>>

AcquireRead(t) ==
    /\ thread_state[t] = "idle"
    /\ LET can_read == (lock \b_and (WRITER \b_or BEING_UPGRADED)) = 0 IN
       IF can_read
       THEN
            /\ lock' = lock + READER
            /\ thread_state' = [thread_state EXCEPT ![t] = "reading"]
            /\ UNCHANGED <<wait_queue>>
       ELSE
            /\ thread_state' = [thread_state EXCEPT ![t] = "waiting_read"]
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED <<lock>>

AcquireWrite(t) ==
    /\ thread_state[t] = "idle"
    /\ IF lock = 0
       THEN
            /\ lock' = WRITER
            /\ thread_state' = [thread_state EXCEPT ![t] = "writing"]
            /\ UNCHANGED <<wait_queue>>
       ELSE
            /\ thread_state' = [thread_state EXCEPT ![t] = "waiting_write"]
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED <<lock>>

AcquireUpRead(t) ==
    /\ thread_state[t] = "idle"
    /\ LET can_upread == (lock \b_and (WRITER \b_or UPGRADEABLE_READER)) = 0 IN
       IF can_upread
       THEN
            /\ lock' = lock \b_or UPGRADEABLE_READER
            /\ thread_state' = [thread_state EXCEPT ![t] = "upreading"]
            /\ UNCHANGED <<wait_queue>>
       ELSE
            /\ thread_state' = [thread_state EXCEPT ![t] = "waiting_upread"]
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED <<lock>>

ReleaseRead(t) ==
    /\ thread_state[t] = "reading"
    /\ LET old_lock == lock IN
       /\ lock' = old_lock - READER
       /\ IF old_lock = READER
          THEN
               IF wait_queue /= <<>>
               THEN LET woken_t == Head(wait_queue) IN
                    /\ thread_state' = [thread_state EXCEPT ![i \in {t, woken_t}] = "idle"]
                    /\ wait_queue' = Tail(wait_queue)
               ELSE
                    /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
                    /\ UNCHANGED <<wait_queue>>
          ELSE
               /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
               /\ UNCHANGED <<wait_queue>>

ReleaseWrite(t) ==
    /\ thread_state[t] = "writing"
    /\ lock' = lock \b_and (\b_not WRITER)
    /\ LET ToIdle == {t} \union AsSet(wait_queue) IN
       /\ thread_state' = [thread_state EXCEPT ![i \in ToIdle] = "idle"]
    /\ wait_queue' = <<>>

ReleaseUpRead(t) ==
    /\ thread_state[t] = "upreading"
    /\ LET old_lock == lock IN
       /\ lock' = old_lock - UPGRADEABLE_READER
       /\ IF old_lock = UPGRADEABLE_READER
          THEN
               LET ToIdle == {t} \union AsSet(wait_queue) IN
               /\ thread_state' = [thread_state EXCEPT ![i \in ToIdle] = "idle"]
               /\ wait_queue' = <<>>
          ELSE
               /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]
               /\ UNCHANGED <<wait_queue>>

StartUpgrade(t) ==
    /\ thread_state[t] = "upreading"
    /\ lock' = lock \b_or BEING_UPGRADED
    /\ thread_state' = [thread_state EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED <<wait_queue>>

FinishUpgrade(t) ==
    /\ thread_state[t] = "upgrading"
    /\ lock = (UPGRADEABLE_READER \b_or BEING_UPGRADED)
    /\ lock' = WRITER
    /\ thread_state' = [thread_state EXCEPT ![t] = "writing"]
    /\ UNCHANGED <<wait_queue>>

Downgrade(t) ==
    /\ thread_state[t] = "writing"
    /\ lock = WRITER
    /\ lock' = UPGRADEABLE_READER
    /\ thread_state' = [thread_state EXCEPT ![t] = "upreading"]
    /\ UNCHANGED <<wait_queue>>

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

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
