---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Integers, Bitwise

CONSTANTS
    Threads,
    NoHolder,
    WRITER,
    UPGRADEABLE_READER,
    BEING_UPGRADED,
    READER_UNIT

ASSUME
    /\ Threads = {"t1", "t2"}
    /\ NoHolder = "NoHolder"
    /\ WRITER = 256
    /\ UPGRADEABLE_READER = 128
    /\ BEING_UPGRADED = 64
    /\ READER_UNIT = 1
    /\ NoHolder \notin Threads

VARIABLES
    lock_state,
    active_readers,
    active_writer,
    active_up_reader,
    wait_queue,
    wake_mode

vars == <<lock_state, active_readers, active_writer, active_up_reader, wait_queue, wake_mode>>

FLAG_MASK == WRITER \blor UPGRADEABLE_READER \blor BEING_UPGRADED

HasWriter(s) == (s \bland WRITER) # 0
HasUpReader(s) == (s \bland UPGRADEABLE_READER) # 0
IsUpgrading(s) == (s \bland BEING_UPGRADED) # 0
ReaderCount(s) == s - (s \bland FLAG_MASK)

IsIdle(t) ==
    /\ t \notin active_readers
    /\ active_writer # t
    /\ active_up_reader # t
    /\ \A i \in DOMAIN wait_queue : wait_queue[i][2] # t

TypeOK ==
    /\ lock_state \in Nat
    /\ active_readers \subseteq Threads
    /\ active_writer \in Threads \cup {NoHolder}
    /\ active_up_reader \in Threads \cup {NoHolder}
    /\ wait_queue \in Seq( {"read", "write", "upread"} \X Threads )
    /\ wake_mode \in {"none", "one", "all"}
    /\ (HasWriter(lock_state) <=> active_writer # NoHolder)
    /\ (HasUpReader(lock_state) \/ IsUpgrading(lock_state) <=> active_up_reader # NoHolder)
    /\ (ReaderCount(lock_state) = Cardinality(active_readers) * READER_UNIT)
    /\ IsUpgrading(lock_state) => HasUpReader(lock_state)
    /\ active_writer # NoHolder => active_readers = {} /\ active_up_reader = NoHolder
    /\ active_up_reader # NoHolder => active_writer = NoHolder
    /\ Cardinality({active_writer, active_up_reader} \ {NoHolder}) <= 1

Init ==
    /\ lock_state = 0
    /\ active_readers = {}
    /\ active_writer = NoHolder
    /\ active_up_reader = NoHolder
    /\ wait_queue = <<>>
    /\ wake_mode = "none"

RequestRead(t) ==
    /\ IsIdle(t)
    /\ IF (lock_state \bland (WRITER \blor UPGRADEABLE_READER \blor BEING_UPGRADED)) = 0
       THEN /\ lock_state' = lock_state + READER_UNIT
            /\ active_readers' = active_readers \cup {t}
            /\ UNCHANGED <<active_writer, active_up_reader, wait_queue, wake_mode>>
       ELSE /\ wait_queue' = Append(wait_queue, <<"read", t>>)
            /\ UNCHANGED <<lock_state, active_readers, active_writer, active_up_reader, wake_mode>>

ReleaseRead(t) ==
    LET new_lock_state == lock_state - READER_UNIT
    IN
    /\ t \in active_readers
    /\ active_readers' = active_readers \ {t}
    /\ IF ReaderCount(new_lock_state) = 0 /\ IsUpgrading(new_lock_state)
       THEN /\ lock_state' = WRITER
            /\ active_writer' = active_up_reader
            /\ active_up_reader' = NoHolder
            /\ wake_mode' = wake_mode
            /\ UNCHANGED <<wait_queue>>
       ELSE /\ lock_state' = new_lock_state
            /\ IF ReaderCount(new_lock_state) = 0
               THEN /\ wake_mode' = "one"
               ELSE /\ wake_mode' = wake_mode
            /\ UNCHANGED <<active_writer, active_up_reader, wait_queue>>

RequestWrite(t) ==
    /\ IsIdle(t)
    /\ IF lock_state = 0
       THEN /\ lock_state' = WRITER
            /\ active_writer' = t
            /\ UNCHANGED <<active_readers, active_up_reader, wait_queue, wake_mode>>
       ELSE /\ wait_queue' = Append(wait_queue, <<"write", t>>)
            /\ UNCHANGED <<lock_state, active_readers, active_writer, active_up_reader, wake_mode>>

ReleaseWrite(t) ==
    /\ active_writer = t
    /\ lock_state' = 0
    /\ active_writer' = NoHolder
    /\ wake_mode' = "all"
    /\ UNCHANGED <<active_readers, active_up_reader, wait_queue>>

RequestUpRead(t) ==
    /\ IsIdle(t)
    /\ IF (lock_state \bland (WRITER \blor UPGRADEABLE_READER)) = 0
       THEN /\ lock_state' = lock_state \blor UPGRADEABLE_READER
            /\ active_up_reader' = t
            /\ UNCHANGED <<active_readers, active_writer, wait_queue, wake_mode>>
       ELSE /\ wait_queue' = Append(wait_queue, <<"upread", t>>)
            /\ UNCHANGED <<lock_state, active_readers, active_writer, active_up_reader, wake_mode>>

ReleaseUpRead(t) ==
    /\ active_up_reader = t
    /\ \lnot IsUpgrading(lock_state)
    /\ lock_state' = lock_state - UPGRADEABLE_READER
    /\ active_up_reader' = NoHolder
    /\ wake_mode' = "all"
    /\ UNCHANGED <<active_readers, active_writer, wait_queue>>

Upgrade(t) ==
    /\ active_up_reader = t
    /\ \lnot IsUpgrading(lock_state)
    /\ IF ReaderCount(lock_state) = 0
       THEN /\ lock_state' = (lock_state - UPGRADEABLE_READER) \blor WRITER
            /\ active_writer' = t
            /\ active_up_reader' = NoHolder
            /\ UNCHANGED <<active_readers, wait_queue, wake_mode>>
       ELSE /\ lock_state' = lock_state \blor BEING_UPGRADED
            /\ UNCHANGED <<active_readers, active_writer, active_up_reader, wait_queue, wake_mode>>

Downgrade(t) ==
    /\ active_writer = t
    /\ lock_state' = (lock_state - WRITER) \blor UPGRADEABLE_READER
    /\ active_writer' = NoHolder
    /\ active_up_reader' = t
    /\ wake_mode' = "all"
    /\ UNCHANGED <<active_readers, wait_queue>>

RECURSIVE GetWokenReadersPrefix
GetWokenReadersPrefix(q) ==
    IF q = <<>> \/ Head(q)[1] # "read" THEN
        << >>
    ELSE
        <<Head(q)>> \o GetWokenReadersPrefix(Tail(q))

ProcessWakeup ==
    /\ wake_mode # "none"
    /\ wait_queue /= <<>>
    /\ wake_mode' = "none"
    /\ LET head_req == Head(wait_queue)
       IN
       IF wake_mode = "one"
       THEN IF head_req[1] = "write" /\ lock_state = 0
            THEN /\ wait_queue' = Tail(wait_queue)
                 /\ lock_state' = WRITER
                 /\ active_writer' = head_req[2]
                 /\ UNCHANGED <<active_readers, active_up_reader>>
            ELSE UNCHANGED vars
       ELSE /\ wake_mode = "all"
            /\ IF head_req[1] = "write" /\ lock_state = 0
               THEN /\ wait_queue' = Tail(wait_queue)
                    /\ lock_state' = WRITER
                    /\ active_writer' = head_req[2]
                    /\ UNCHANGED <<active_readers, active_up_reader>>
               ELSE IF head_req[1] = "upread" /\ (lock_state \bland (WRITER \blor UPGRADEABLE_READER)) = 0
                    THEN /\ wait_queue' = Tail(wait_queue)
                         /\ lock_state' = lock_state \blor UPGRADEABLE_READER
                         /\ active_up_reader' = head_req[2]
                         /\ UNCHANGED <<active_readers, active_writer>>
                    ELSE IF head_req[1] = "read" /\ (lock_state \bland (WRITER \blor UPGRADEABLE_READER \blor BEING_UPGRADED)) = 0
                         THEN LET woken_reqs == GetWokenReadersPrefix(wait_queue)
                                  woken_threads == {woken_reqs[i][2] : i \in DOMAIN woken_reqs}
                              IN /\ wait_queue' = SubSeq(wait_queue, Len(woken_reqs) + 1, Len(wait_queue))
                                 /\ lock_state' = lock_state + (Cardinality(woken_threads) * READER_UNIT)
                                 /\ active_readers' = active_readers \cup woken_threads
                                 /\ UNCHANGED <<active_writer, active_up_reader>>
                         ELSE UNCHANGED vars

ThreadAction(t) ==
    \/ RequestRead(t)
    \/ ReleaseRead(t)
    \/ RequestWrite(t)
    \/ ReleaseWrite(t)
    \/ RequestUpRead(t)
    \/ ReleaseUpRead(t)
    \/ Upgrade(t)
    \/ Downgrade(t)

Next ==
    \/ (\E t \in Threads: ThreadAction(t))
    \/ ProcessWakeup

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
