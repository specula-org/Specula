---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Thread, None

VARIABLES lock_state, wait_queue, active_readers, active_writer, active_upgradable, upgrading_thread

vars == <<lock_state, wait_queue, active_readers, active_writer, active_upgradable, upgrading_thread>>

TypeOK ==
    /\ lock_state \in [ writer: BOOLEAN, upgradable: BOOLEAN, upgrading: BOOLEAN, readers: Nat ]
    /\ wait_queue \in Seq(Thread)
    /\ active_readers \subseteq Thread
    /\ active_writer \in Thread \cup {None}
    /\ active_upgradable \in Thread \cup {None}
    /\ upgrading_thread \in Thread \cup {None}

Init ==
    /\ lock_state = [writer |-> FALSE, upgradable |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ wait_queue = << >>
    /\ active_readers = {}
    /\ active_writer = None
    /\ active_upgradable = None
    /\ upgrading_thread = None

IsIdle(t) ==
    /\ t \notin active_readers
    /\ t # active_writer
    /\ t # active_upgradable
    /\ t # upgrading_thread
    /\ \forall i \in DOMAIN wait_queue: wait_queue[i] # t

CanRead == lock_state.writer = FALSE /\ lock_state.upgrading = FALSE
CanWrite == lock_state.writer = FALSE /\ lock_state.upgradable = FALSE /\ lock_state.readers = 0
CanUpread == lock_state.writer = FALSE /\ lock_state.upgradable = FALSE

RequestRead(t) ==
    /\ IsIdle(t)
    /\ IF CanRead THEN
        /\ active_readers' = active_readers \cup {t}
        /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
        /\ UNCHANGED <<wait_queue, active_writer, active_upgradable, upgrading_thread>>
       ELSE
        /\ wait_queue' = Append(wait_queue, t)
        /\ UNCHANGED <<lock_state, active_readers, active_writer, active_upgradable, upgrading_thread>>

RequestWrite(t) ==
    /\ IsIdle(t)
    /\ IF CanWrite THEN
        /\ active_writer' = t
        /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
        /\ UNCHANGED <<wait_queue, active_readers, active_upgradable, upgrading_thread>>
       ELSE
        /\ wait_queue' = Append(wait_queue, t)
        /\ UNCHANGED <<lock_state, active_readers, active_writer, active_upgradable, upgrading_thread>>

RequestUpgradable(t) ==
    /\ IsIdle(t)
    /\ IF CanUpread THEN
        /\ active_upgradable' = t
        /\ lock_state' = [lock_state EXCEPT !.upgradable = TRUE]
        /\ UNCHANGED <<wait_queue, active_readers, active_writer, upgrading_thread>>
       ELSE
        /\ wait_queue' = Append(wait_queue, t)
        /\ UNCHANGED <<lock_state, active_readers, active_writer, active_upgradable, upgrading_thread>>

ReleaseRead(t) ==
    /\ t \in active_readers
    /\ LET new_readers == lock_state.readers - 1
    IN /\ active_readers' = active_readers \ {t}
       /\ IF new_readers = 0 /\ wait_queue /= << >> THEN
            (* FIX: Corrected a parse error. The error message suggests a malformed LET expression. *)
            (* A likely cause is a typo where `IN` was written as `LET`. The syntax is now corrected *)
            (* to use `LET ... IN ...` properly. *)
            LET waiter = Head(wait_queue) IN
            IF lock_state.writer = FALSE /\ lock_state.upgradable = FALSE THEN
                /\ active_writer' = waiter
                /\ lock_state' = [writer |-> TRUE, upgradable |-> FALSE, upgrading |-> FALSE, readers |-> 0]
                /\ wait_queue' = Tail(wait_queue)
                /\ UNCHANGED <<active_upgradable, upgrading_thread>>
            ELSE
                /\ lock_state' = [lock_state EXCEPT !.readers = new_readers]
                /\ UNCHANGED <<wait_queue, active_writer, active_upgradable, upgrading_thread>>
        ELSE
            /\ lock_state' = [lock_state EXCEPT !.readers = new_readers]
            /\ UNCHANGED <<wait_queue, active_writer, active_upgradable, upgrading_thread>>

ReleaseWrite(t) ==
    /\ active_writer = t
    /\ active_writer' = None
    /\ LET new_lock_state = [lock_state EXCEPT !.writer = FALSE]
    IN /\ IF wait_queue /= << >> THEN
            LET waiter = Head(wait_queue) IN
            IF new_lock_state.upgradable = FALSE THEN
                /\ active_upgradable' = waiter
                /\ lock_state' = [new_lock_state EXCEPT !.upgradable = TRUE]
                /\ wait_queue' = Tail(wait_queue)
                /\ UNCHANGED <<active_readers, upgrading_thread>>
            ELSE IF new_lock_state.upgrading = FALSE THEN
                LET readers_to_acquire = {wait_queue[i] : i \in 1..Len(wait_queue)}
                IN /\ active_readers' = active_readers \cup readers_to_acquire
                   /\ lock_state' = [new_lock_state EXCEPT !.readers = @ + Len(readers_to_acquire)]
                   /\ wait_queue' = << >>
                   /\ UNCHANGED <<active_upgradable, upgrading_thread>>
            ELSE
                /\ lock_state' = new_lock_state
                /\ UNCHANGED <<wait_queue, active_readers, active_upgradable, upgrading_thread>>
        ELSE
            /\ lock_state' = new_lock_state
            /\ UNCHANGED <<wait_queue, active_readers, active_upgradable, upgrading_thread>>

ReleaseUpgradable(t) ==
    /\ active_upgradable = t
    /\ upgrading_thread # t
    /\ active_upgradable' = None
    /\ LET new_lock_state = [lock_state EXCEPT !.upgradable = FALSE]
    IN /\ IF wait_queue /= << >> THEN
            LET waiter = Head(wait_queue) IN
            IF new_lock_state.writer = FALSE /\ new_lock_state.readers = 0 THEN
                /\ active_writer' = waiter
                /\ lock_state' = [new_lock_state EXCEPT !.writer = TRUE]
                /\ wait_queue' = Tail(wait_queue)
                /\ UNCHANGED <<active_readers, upgrading_thread>>
            ELSE IF new_lock_state.writer = FALSE /\ new_lock_state.upgrading = FALSE THEN
                (* FIX: Corrected a parse error. A LET definition cannot be part of a conjunction. *)
                (* The original code had `/\ LET ...`, which is a syntax error. The fix wraps the *)
                (* subsequent conjunction in a `LET ... IN (...)` block to make it syntactically correct *)
                (* while preserving the original logic. *)
                LET readers_to_acquire = {wait_queue[i] : i \in 1..Len(wait_queue)}
                IN /\ active_readers' = active_readers \cup readers_to_acquire
                   /\ lock_state' = [new_lock_state EXCEPT !.readers = @ + Len(readers_to_acquire)]
                   /\ wait_queue' = << >>
                   /\ UNCHANGED <<active_writer, upgrading_thread>>
            ELSE
                /\ lock_state' = new_lock_state
                /\ UNCHANGED <<wait_queue, active_readers, active_writer, upgrading_thread>>
        ELSE
            /\ lock_state' = new_lock_state
            /\ UNCHANGED <<wait_queue, active_readers, active_writer, upgrading_thread>>

StartUpgrade(t) ==
    /\ active_upgradable = t
    /\ upgrading_thread = None
    /\ upgrading_thread' = t
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]
    /\ UNCHANGED <<wait_queue, active_readers, active_writer, active_upgradable>>

CompleteUpgrade(t) ==
    /\ upgrading_thread = t
    /\ lock_state.readers = 0
    /\ upgrading_thread' = None
    /\ active_upgradable' = None
    /\ active_writer' = t
    /\ lock_state' = [writer |-> TRUE, upgradable |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ UNCHANGED <<wait_queue, active_readers>>

Downgrade(t) ==
    /\ active_writer = t
    /\ active_writer' = None
    /\ active_upgradable' = t
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upgradable = TRUE]
    /\ UNCHANGED <<wait_queue, active_readers, upgrading_thread>>

Next ==
    \/ \E t \in Thread: RequestRead(t)
    \/ \E t \in Thread: RequestWrite(t)
    \/ \E t \in Thread: RequestUpgradable(t)
    \/ \E t \in Thread: ReleaseRead(t)
    \/ \E t \in Thread: ReleaseWrite(t)
    \/ \E t \in Thread: ReleaseUpgradable(t)
    \/ \E t \in Thread: StartUpgrade(t)
    \/ \E t \in Thread: CompleteUpgrade(t)
    \/ \E t \in Thread: Downgrade(t)

Progress(t) ==
    \/ ReleaseRead(t)
    \/ ReleaseWrite(t)
    \/ ReleaseUpgradable(t)
    \/ StartUpgrade(t)
    \/ CompleteUpgrade(t)
    \/ Downgrade(t)

Spec == Init /\ [][Next]_vars /\ \A t \in Thread : WF_vars(Progress(t))

====