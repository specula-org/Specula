---- MODULE rwmutex ----
EXTENDS Sequences, FiniteSets, Integers

CONSTANTS Threads

ASSUME Threads \subseteq Nat

VARIABLES lock_state, pc, wait_queue

vars == << lock_state, pc, wait_queue >>

PCStates == {"idle", "reading", "writing", "upreading", "upgrading", "waiting"}
RequestTypes == {"read", "write", "upread"}

TypeOK ==
    /\ lock_state \in [ writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: Nat ]
    /\ pc \in [ Threads -> PCStates ]
    /\ wait_queue \in Seq(Threads \X RequestTypes)

Init ==
    /\ lock_state = [ writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0 ]
    /\ pc = [ t \in Threads |-> "idle" ]
    /\ wait_queue = <<>>

(*-- Actions for threads to request locks --*)

CanAcquireRead(lock) == lock.writer = FALSE /\ lock.upgrading = FALSE
CanAcquireWrite(lock) == lock.writer = FALSE /\ lock.upreader = FALSE /\ lock.readers = 0
CanAcquireUpread(lock) == lock.writer = FALSE /\ lock.upreader = FALSE

RequestRead(t) ==
    /\ pc[t] = "idle"
    /\ IF CanAcquireRead(lock_state)
       THEN /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
            /\ pc' = [pc EXCEPT ![t] = "reading"]
            /\ UNCHANGED wait_queue
       ELSE /\ pc' = [pc EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, <<t, "read">>)
            /\ UNCHANGED lock_state

RequestWrite(t) ==
    /\ pc[t] = "idle"
    /\ IF CanAcquireWrite(lock_state)
       THEN /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
            /\ pc' = [pc EXCEPT ![t] = "writing"]
            /\ UNCHANGED wait_queue
       ELSE /\ pc' = [pc EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, <<t, "write">>)
            /\ UNCHANGED lock_state

RequestUpread(t) ==
    /\ pc[t] = "idle"
    /\ IF CanAcquireUpread(lock_state)
       THEN /\ lock_state' = [lock_state EXCEPT !.upreader = TRUE]
            /\ pc' = [pc EXCEPT ![t] = "upreading"]
            /\ UNCHANGED wait_queue
       ELSE /\ pc' = [pc EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, <<t, "upread">>)
            /\ UNCHANGED lock_state

(*-- Actions for threads to release locks --*)

ReleaseRead(t) ==
    /\ pc[t] = "reading"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock_state' = [lock_state EXCEPT !.readers = @ - 1]
    /\ UNCHANGED wait_queue

ReleaseWrite(t) ==
    /\ pc[t] = "writing"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ UNCHANGED wait_queue

ReleaseUpread(t) ==
    /\ pc[t] = "upreading"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock_state' = [lock_state EXCEPT !.upreader = FALSE]
    /\ UNCHANGED wait_queue

(*-- Actions for upgradeable reader --*)

StartUpgrade(t) ==
    /\ pc[t] = "upreading"
    /\ pc' = [pc EXCEPT ![t] = "upgrading"]
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]
    /\ UNCHANGED wait_queue

CompleteUpgrade(t) ==
    /\ pc[t] = "upgrading"
    /\ lock_state.readers = 0
    /\ pc' = [pc EXCEPT ![t] = "writing"]
    /\ lock_state' = [ writer |-> TRUE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0 ]
    /\ UNCHANGED wait_queue

Downgrade(t) ==
    /\ pc[t] = "writing"
    /\ lock_state.writer = TRUE
    /\ lock_state.upreader = FALSE
    /\ lock_state.upgrading = FALSE
    /\ lock_state.readers = 0
    /\ pc' = [pc EXCEPT ![t] = "upreading"]
    /\ lock_state' = [ writer |-> FALSE, upreader |-> TRUE, upgrading |-> FALSE, readers |-> 0 ]
    /\ UNCHANGED wait_queue

(*-- Action to service the wait queue, modeling wakeups --*)

ServiceWaitQueue ==
    /\ Len(wait_queue) > 0
    /\ LET head_req == Head(wait_queue)
           head_thread == head_req[1]
           head_type == head_req[2]
    IN
    \/ /\ head_type = "write"
       /\ CanAcquireWrite(lock_state)
       /\ pc' = [pc EXCEPT ![head_thread] = "writing"]
       /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
       /\ wait_queue' = Tail(wait_queue)
    \/ /\ head_type \in {"read", "upread"}
       /\ CanAcquireRead(lock_state)
       /\ LET
            \* Find the index of the first request in the queue that cannot be woken.
            \* A request cannot be woken if it's a writer, or if it's an upreader
            \* and an upreader is already active or is part of the group being woken.
            first_writer_idx ==
                IF \E i \in 1..Len(wait_queue) : wait_queue[i][2] = "write"
                THEN Min({i \in 1..Len(wait_queue) : wait_queue[i][2] = "write"})
                ELSE Len(wait_queue) + 1

            first_non_wakeable_upreader_idx ==
                IF lock_state.upreader
                THEN \* An upreader is active, so the first waiting upreader is a blocker.
                     IF \E i \in 1..Len(wait_queue) : wait_queue[i][2] = "upread"
                     THEN Min({i \in 1..Len(wait_queue) : wait_queue[i][2] = "upread"})
                     ELSE Len(wait_queue) + 1
                ELSE \* No upreader is active, so the second waiting upreader is a blocker.
                     IF Cardinality({i \in 1..Len(wait_queue) : wait_queue[i][2] = "upread"}) >= 2
                     THEN LET upreader_indices == {i \in 1..Len(wait_queue) : wait_queue[i][2] = "upread"}
                               first_up_idx == Min(upreader_indices)
                          IN Min(upreader_indices \ {first_up_idx})
                     ELSE Len(wait_queue) + 1

            first_blocker_idx == Min({first_writer_idx, first_non_wakeable_upreader_idx})
            woken_reqs_seq == SubSeq(wait_queue, 1, first_blocker_idx - 1)
            woken_threads == {req[1] : req \in {woken_reqs_seq[i] : i \in DOMAIN woken_reqs_seq}}

            new_pc == [ t \in Threads |->
                          IF t \in woken_threads THEN
                              IF <<t, "read">> \in {woken_reqs_seq[i] : i \in DOMAIN woken_reqs_seq}
                              THEN "reading"
                              ELSE "upreading"
                          ELSE pc[t] ]

            num_new_readers == Cardinality({i \in DOMAIN woken_reqs_seq : woken_reqs_seq[i][2] = "read"})
            has_new_upreader == \E i \in DOMAIN woken_reqs_seq : woken_reqs_seq[i][2] = "upread"
          IN
          /\ Len(woken_reqs_seq) > 0
          /\ pc' = new_pc
          /\ lock_state' = [ lock_state EXCEPT !.readers = @ + num_new_readers,
                                              !.upreader = (@ \/ has_new_upreader) ]
          /\ wait_queue' = SubSeq(wait_queue, first_blocker_idx, Len(wait_queue))

ThreadAction(t) ==
    \/ RequestRead(t)
    \/ RequestWrite(t)
    \/ RequestUpread(t)
    \/ ReleaseRead(t)
    \/ ReleaseWrite(t)
    \/ ReleaseUpread(t)
    \/ StartUpgrade(t)
    \/ CompleteUpgrade(t)
    \/ Downgrade(t)

Next ==
    \/ \E t \in Threads: ThreadAction(t)
    \/ ServiceWaitQueue

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
