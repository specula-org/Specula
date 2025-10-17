---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, None

VARIABLES
    lock,
    writer_holder,
    upreader_holder,
    upgrading_holder,
    reader_holders,
    wait_queue

vars == <<lock, writer_holder, upreader_holder, upgrading_holder, reader_holders, wait_queue>>

LockType == {"read", "write", "upread"}

ActiveThreads ==
    ({writer_holder, upreader_holder, upgrading_holder} \setminus {None})
    \cup reader_holders
    \* FIX: The original set comprehension `{{{{... : q \in wait_queue}}}}` is not valid syntax for iterating over a sequence.
    \* Changed to iterate over the domain of the sequence `i \in DOMAIN wait_queue` and access elements by index `wait_queue[i]`.
    \cup {wait_queue[i].thread : i \in DOMAIN wait_queue}

Init ==
    /\ lock = [writer_bit |-> FALSE, upreader_bit |-> FALSE, upgrading_bit |-> FALSE, reader_count |-> 0]
    /\ writer_holder = None
    /\ upreader_holder = None
    /\ upgrading_holder = None
    /\ reader_holders = {}
    /\ wait_queue = <<>>

TypeOK ==
    /\ lock \in [writer_bit: BOOLEAN, upreader_bit: BOOLEAN, upgrading_bit: BOOLEAN, reader_count: Nat]
    /\ writer_holder \in Threads \cup {None}
    /\ upreader_holder \in Threads \cup {None}
    /\ upgrading_holder \in Threads \cup {None}
    /\ reader_holders \subseteq Threads
    /\ wait_queue \in Seq([thread: Threads, type: LockType])

CanAcquire(req, current_lock) ==
    CASE req.type = "read" ->
        /\ \lnot current_lock.writer_bit
        /\ \lnot current_lock.upgrading_bit
      [] req.type = "write" ->
        /\ \lnot current_lock.writer_bit
        /\ \lnot current_lock.upreader_bit
        /\ current_lock.reader_count = 0
      [] req.type = "upread" ->
        /\ \lnot current_lock.writer_bit
        /\ \lnot current_lock.upreader_bit

Request(t, type) ==
    /\ t \in Threads
    /\ t # None
    /\ t \notin ActiveThreads
    /\ type \in LockType
    /\ wait_queue' = Append(wait_queue, [thread |-> t, type |-> type])
    /\ UNCHANGED <<lock, writer_holder, upreader_holder, upgrading_holder, reader_holders>>

Acquire ==
    \E idx \in DOMAIN wait_queue:
        LET req == wait_queue[idx] IN
        /\ CanAcquire(req, lock)
        /\ \A j \in 1..(idx - 1): \lnot CanAcquire(wait_queue[j], lock)
        /\ wait_queue' = SubSeq(wait_queue, 1, idx - 1) \o SubSeq(wait_queue, idx + 1, Len(wait_queue))
        /\ CASE req.type = "read" ->
                /\ lock' = [lock EXCEPT !.reader_count = @ + 1]
                /\ reader_holders' = reader_holders \cup {req.thread}
                /\ UNCHANGED <<writer_holder, upreader_holder, upgrading_holder>>
           [] req.type = "write" ->
                /\ lock' = [lock EXCEPT !.writer_bit = TRUE]
                /\ writer_holder' = req.thread
                /\ UNCHANGED <<reader_holders, upreader_holder, upgrading_holder>>
           [] req.type = "upread" ->
                /\ lock' = [lock EXCEPT !.upreader_bit = TRUE]
                /\ upreader_holder' = req.thread
                /\ UNCHANGED <<reader_holders, writer_holder, upgrading_holder>>

ReleaseRead(t) ==
    /\ t \in reader_holders
    /\ reader_holders' = reader_holders \setminus {t}
    /\ lock' = [lock EXCEPT !.reader_count = @ - 1]
    /\ UNCHANGED <<writer_holder, upreader_holder, upgrading_holder, wait_queue>>

ReleaseWrite(t) ==
    /\ writer_holder = t
    /\ writer_holder' = None
    /\ lock' = [lock EXCEPT !.writer_bit = FALSE]
    /\ UNCHANGED <<upreader_holder, upgrading_holder, reader_holders, wait_queue>>

ReleaseUpRead(t) ==
    /\ upreader_holder = t
    /\ upreader_holder' = None
    /\ lock' = [lock EXCEPT !.upreader_bit = FALSE]
    /\ UNCHANGED <<writer_holder, upgrading_holder, reader_holders, wait_queue>>

StartUpgrade(t) ==
    /\ upreader_holder = t
    /\ upreader_holder' = None
    /\ upgrading_holder' = t
    /\ lock' = [lock EXCEPT !.upreader_bit = FALSE, !.upgrading_bit = TRUE]
    /\ UNCHANGED <<writer_holder, reader_holders, wait_queue>>

CompleteUpgrade(t) ==
    /\ upgrading_holder = t
    /\ lock.reader_count = 0
    /\ upgrading_holder' = None
    /\ writer_holder' = t
    /\ lock' = [lock EXCEPT !.upgrading_bit = FALSE, !.writer_bit = TRUE]
    /\ UNCHANGED <<upreader_holder, reader_holders, wait_queue>>

Downgrade(t) ==
    /\ writer_holder = t
    /\ writer_holder' = None
    /\ upreader_holder' = t
    /\ lock' = [lock EXCEPT !.writer_bit = FALSE, !.upreader_bit = TRUE]
    /\ UNCHANGED <<upgrading_holder, reader_holders, wait_queue>>

Next ==
    \/ Acquire
    \/ \E t \in Threads, type \in LockType: Request(t, type)
    \/ \E t \in Threads:
        \/ ReleaseRead(t)
        \/ ReleaseWrite(t)
        \/ ReleaseUpRead(t)
        \/ StartUpgrade(t)
        \/ CompleteUpgrade(t)
        \/ Downgrade(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
