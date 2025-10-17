---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Proc

VARIABLES lock_state, wait_queue, proc_state

vars == <<lock_state, wait_queue, proc_state>>

TypeOK ==
    /\ lock_state \in [ writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: Nat ]
    /\ wait_queue \in Seq([id: Proc, op: {{"read", "write", "upread"}}])
    /\ proc_state \in [Proc -> {{"idle", "waiting", "reading", "writing", "upreading", "upgrading"}}]

Init ==
    /\ lock_state = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ wait_queue = <<>>
    /\ proc_state = [p \in Proc |-> "idle"]

RequestRead(p) ==
    /\ proc_state[p] = "idle"
    /\ IF lock_state.writer = FALSE /\ lock_state.upgrading = FALSE THEN
        /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
        /\ proc_state' = [proc_state EXCEPT ![p] = "reading"]
        /\ UNCHANGED wait_queue
    ELSE
        /\ wait_queue' = Append(wait_queue, [id |-> p, op |-> "read"])
        /\ proc_state' = [proc_state EXCEPT ![p] = "waiting"]
        /\ UNCHANGED lock_state

RequestWrite(p) ==
    /\ proc_state[p] = "idle"
    /\ IF lock_state.writer = FALSE /\ lock_state.upreader = FALSE /\ lock_state.readers = 0 THEN
        /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
        /\ proc_state' = [proc_state EXCEPT ![p] = "writing"]
        /\ UNCHANGED wait_queue
    ELSE
        /\ wait_queue' = Append(wait_queue, [id |-> p, op |-> "write"])
        /\ proc_state' = [proc_state EXCEPT ![p] = "waiting"]
        /\ UNCHANGED lock_state

RequestUpRead(p) ==
    /\ proc_state[p] = "idle"
    /\ IF lock_state.writer = FALSE /\ lock_state.upreader = FALSE THEN
        /\ lock_state' = [lock_state EXCEPT !.upreader = TRUE]
        /\ proc_state' = [proc_state EXCEPT ![p] = "upreading"]
        /\ UNCHANGED wait_queue
    ELSE
        /\ wait_queue' = Append(wait_queue, [id |-> p, op |-> "upread"])
        /\ proc_state' = [proc_state EXCEPT ![p] = "waiting"]
        /\ UNCHANGED lock_state

ReleaseRead(p) ==
    /\ proc_state[p] = "reading"
    /\ LET new_readers == lock_state.readers - 1
    IN
        /\ lock_state' = [lock_state EXCEPT !.readers = new_readers]
        /\ IF new_readers = 0 /\ Len(wait_queue) > 0 THEN
            /\ LET awakened_proc_id == Head(wait_queue).id
            /\ wait_queue' = Tail(wait_queue)
            /\ proc_state' = [proc_state EXCEPT ![p] = "idle", ![awakened_proc_id] = "idle"]
        /\ ELSE
            /\ wait_queue' = wait_queue
            /\ proc_state' = [proc_state EXCEPT ![p] = "idle"]

ReleaseWrite(p) ==
    /\ proc_state[p] = "writing"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ LET awakened_ids == {{q.id : q \in SubSeq(wait_queue, 1, Len(wait_queue))}}
    /\ wait_queue' = <<>>
    /\ proc_state' = [q \in Proc |-> IF q = p \/ q \in awakened_ids THEN "idle" ELSE proc_state[q]]

ReleaseUpRead(p) ==
    /\ proc_state[p] = "upreading"
    /\ LET new_lock_state == [lock_state EXCEPT !.upreader = FALSE]
    IN
        /\ lock_state' = new_lock_state
        /\ IF new_lock_state.readers = 0 THEN
            /\ LET awakened_ids == {{q.id : q \in SubSeq(wait_queue, 1, Len(wait_queue))}}
            /\ wait_queue' = <<>>
            /\ proc_state' = [q \in Proc |-> IF q = p \/ q \in awakened_ids THEN "idle" ELSE proc_state[q]]
        /\ ELSE
            /\ wait_queue' = wait_queue
            /\ proc_state' = [proc_state EXCEPT ![p] = "idle"]

StartUpgrade(p) ==
    /\ proc_state[p] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]
    /\ proc_state' = [proc_state EXCEPT ![p] = "upgrading"]
    /\ UNCHANGED wait_queue

CompleteUpgrade(p) ==
    /\ proc_state[p] = "upgrading"
    /\ lock_state.readers = 0
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.upreader = FALSE, !.upgrading = FALSE]
    /\ proc_state' = [proc_state EXCEPT ![p] = "writing"]
    /\ UNCHANGED wait_queue

Downgrade(p) ==
    /\ proc_state[p] = "writing"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upreader = TRUE]
    /\ proc_state' = [proc_state EXCEPT ![p] = "upreading"]
    /\ UNCHANGED wait_queue

Next ==
    \E p \in Proc :
        \/ RequestRead(p)
        \/ RequestWrite(p)
        \/ RequestUpRead(p)
        \/ ReleaseRead(p)
        \/ ReleaseWrite(p)
        \/ ReleaseUpRead(p)
        \/ StartUpgrade(p)
        \/ CompleteUpgrade(p)
        \/ Downgrade(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
