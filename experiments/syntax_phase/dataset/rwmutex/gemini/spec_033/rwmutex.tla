---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads
ASSUME Threads \subseteq Nat

WRITER == 2^(63)
UPGRADEABLE_READER == 2^(62)
BEING_UPGRADED == 2^(61)
READER == 1

VARIABLES
    lock,
    queue,
    thread_status,
    reader_guard_count

vars == <<lock, queue, thread_status, reader_guard_count>>

IsSet(l, flag) == (l \div flag) % 2 = 1
ReaderCount(l) == l % BEING_UPGRADED

RECURSIVE Summation(_, _)
Summation(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN
             f[x] + Summation(f, S \ {x})

TypeOK ==
    /\ lock \in Nat
    /\ queue \in Seq(Threads)
    /\ thread_status \in [Threads -> {"idle", "reading", "writing", "upreading", "upgrading", "blocked"}]
    /\ reader_guard_count \in [Threads -> Nat]
    /\ \A t \in Threads: (thread_status[t] = "blocked") <=> (t \in Set(queue))
    /\ \A t \in Threads:
        \/ (thread_status[t] = "reading" /\ reader_guard_count[t] > 0)
        \/ (thread_status[t] /= "reading" /\ reader_guard_count[t] = 0)
    /\ IsSet(lock, WRITER) <=> (\E t \in Threads: thread_status[t] = "writing")
    /\ IsSet(lock, UPGRADEABLE_READER) <=> (\E t \in Threads: thread_status[t] \in {"upreading", "upgrading"})
    /\ IsSet(lock, BEING_UPGRADED) <=> (\E t \in Threads: thread_status[t] = "upgrading")
    /\ ReaderCount(lock) = Summation(reader_guard_count, Threads)
    /\ Cardinality({t \in Threads: thread_status[t] = "writing"}) \in {0, 1}
    /\ Cardinality({t \in Threads: thread_status[t] \in {"upreading", "upgrading"}}) \in {0, 1}

Init ==
    /\ lock = 0
    /\ queue = <<>>
    /\ thread_status = [t \in Threads |-> "idle"]
    /\ reader_guard_count = [t \in Threads |-> 0]

Read(t) ==
    /\ thread_status[t] = "idle"
    /\ IF \lnot IsSet(lock, WRITER) /\ \lnot IsSet(lock, BEING_UPGRADED) THEN
        /\ lock' = lock + READER
        /\ thread_status' = [thread_status EXCEPT ![t] = "reading"]
        /\ reader_guard_count' = [reader_guard_count EXCEPT ![t] = @ + 1]
        /\ UNCHANGED queue
       ELSE
        /\ thread_status' = [thread_status EXCEPT ![t] = "blocked"]
        /\ queue' = Append(queue, t)
        /\ UNCHANGED <<lock, reader_guard_count>>

Write(t) ==
    /\ thread_status[t] = "idle"
    /\ IF lock = 0 THEN
        /\ lock' = WRITER
        /\ thread_status' = [thread_status EXCEPT ![t] = "writing"]
        /\ UNCHANGED <<queue, reader_guard_count>>
       ELSE
        /\ thread_status' = [thread_status EXCEPT ![t] = "blocked"]
        /\ queue' = Append(queue, t)
        /\ UNCHANGED <<lock, reader_guard_count>>

UpRead(t) ==
    /\ thread_status[t] = "idle"
    /\ IF \lnot IsSet(lock, WRITER) /\ \lnot IsSet(lock, UPGRADEABLE_READER) THEN
        /\ lock' = lock + UPGRADEABLE_READER
        /\ thread_status' = [thread_status EXCEPT ![t] = "upreading"]
        /\ UNCHANGED <<queue, reader_guard_count>>
       ELSE
        /\ thread_status' = [thread_status EXCEPT ![t] = "blocked"]
        /\ queue' = Append(queue, t)
        /\ UNCHANGED <<lock, reader_guard_count>>

ReleaseRead(t) ==
    /\ thread_status[t] = "reading"
    /\ LET new_lock == lock - READER
           new_reader_count == reader_guard_count[t] - 1
           new_status == IF new_reader_count = 0
                         THEN [thread_status EXCEPT ![t] = "idle"]
                         ELSE [thread_status EXCEPT ![t] = "reading"]
       IN
       /\ lock' = new_lock
       /\ reader_guard_count' = [reader_guard_count EXCEPT ![t] = new_reader_count]
       /\ IF lock = READER THEN
            IF Len(queue) > 0 THEN
                LET woken_t == Head(queue) IN
                /\ queue' = Tail(queue)
                /\ thread_status' = [new_status EXCEPT ![woken_t] = "idle"]
            ELSE
                /\ thread_status' = new_status
                /\ UNCHANGED queue
         ELSE
            /\ thread_status' = new_status
            /\ UNCHANGED queue

ReleaseWrite(t) ==
    /\ thread_status[t] = "writing"
    /\ lock' = lock - WRITER
    /\ LET woken_threads == Set(queue) IN
       /\ thread_status' = [ s \in Threads |-> IF s = t \/ s \in woken_threads THEN "idle" ELSE thread_status[s] ]
    /\ queue' = <<>>
    /\ UNCHANGED reader_guard_count

ReleaseUpRead(t) ==
    /\ thread_status[t] = "upreading"
    /\ LET old_lock == lock IN
       /\ lock' = lock - UPGRADEABLE_READER
       /\ IF old_lock = UPGRADEABLE_READER THEN
            LET woken_threads == Set(queue) IN
            /\ thread_status' = [ s \in Threads |-> IF s = t \/ s \in woken_threads THEN "idle" ELSE thread_status[s] ]
            /\ queue' = <<>>
         ELSE
            /\ thread_status' = [thread_status EXCEPT ![t] = "idle"]
            /\ UNCHANGED queue
    /\ UNCHANGED reader_guard_count

StartUpgrade(t) ==
    /\ thread_status[t] = "upreading"
    /\ lock' = lock + BEING_UPGRADED
    /\ thread_status' = [thread_status EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED <<queue, reader_guard_count>>

FinishUpgrade(t) ==
    /\ thread_status[t] = "upgrading"
    /\ IsSet(lock, UPGRADEABLE_READER)
    /\ IsSet(lock, BEING_UPGRADED)
    /\ ReaderCount(lock) = 0
    /\ lock' = WRITER
    /\ thread_status' = [thread_status EXCEPT ![t] = "writing"]
    /\ UNCHANGED <<queue, reader_guard_count>>

Downgrade(t) ==
    /\ thread_status[t] = "writing"
    /\ lock' = UPGRADEABLE_READER
    /\ thread_status' = [thread_status EXCEPT ![t] = "upreading"]
    /\ UNCHANGED <<queue, reader_guard_count>>

Next ==
    \E t \in Threads:
        \/ Read(t)
        \/ Write(t)
        \/ UpRead(t)
        \/ ReleaseRead(t)
        \/ ReleaseWrite(t)
        \/ ReleaseUpRead(t)
        \/ StartUpgrade(t)
        \/ FinishUpgrade(t)
        \/ Downgrade(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
