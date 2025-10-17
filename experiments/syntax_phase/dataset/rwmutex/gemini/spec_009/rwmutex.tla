---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

ASSUME Threads \subseteq Nat

VARIABLES lock_state, pc, wait_queue

vars == << lock_state, pc, wait_queue >>

PCStates == {"idle", "reading", "writing", "upreading", "upgrading", "waiting"}
RequestTypes == {"read", "write", "upread"}

TypeOK ==
    /\ lock_state \in [ writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: Nat ]
    /\ pc \in [ Threads -> PCStates ]
    /\ wait_queue \in Seq(Threads)

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
    /\ IF CanAcquireRead(lock_state) THEN
        /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
        /\ pc' = [pc EXCEPT ![t] = "reading"]
        /\ wait_queue' = wait_queue
    /\ ELSE
        /\ pc' = [pc EXCEPT ![t] = "waiting"]
        /\ wait_queue' = Append(wait_queue, t)
        /\ lock_state' = lock_state

RequestWrite(t) ==
    /\ pc[t] = "idle"
    /\ IF CanAcquireWrite(lock_state) THEN
        /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
        /\ pc' = [pc EXCEPT ![t] = "writing"]
        /\ wait_queue' = wait_queue
    /\ ELSE
        /\ pc' = [pc EXCEPT ![t] = "waiting"]
        /\ wait_queue' = Append(wait_queue, t)
        /\ lock_state' = lock_state

RequestUpread(t) ==
    /\ pc[t] = "idle"
    /\ IF CanAcquireUpread(lock_state) THEN
        /\ lock_state' = [lock_state EXCEPT !.upreader = TRUE]
        /\ pc' = [pc EXCEPT ![t] = "upreading"]
        /\ wait_queue' = wait_queue
    /\ ELSE
        /\ pc' = [pc EXCEPT ![t] = "waiting"]
        /\ wait_queue' = Append(wait_queue, t)
        /\ lock_state' = lock_state

(*-- Actions for threads to release locks --*)

ReleaseRead(t) ==
    /\ pc[t] = "reading"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock_state' = [lock_state EXCEPT !.readers = @ - 1]
    /\ wait_queue' = wait_queue

ReleaseWrite(t) ==
    /\ pc[t] = "writing"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ wait_queue' = wait_queue

ReleaseUpread(t) ==
    /\ pc[t] = "upreading"
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ lock_state' = [lock_state EXCEPT !.upreader = FALSE]
    /\ wait_queue' = wait_queue

(*-- Actions for upgradeable reader --*)

StartUpgrade(t) ==
    /\ pc[t] = "upreading"
    /\ pc' = [pc EXCEPT ![t] = "upgrading"]
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]
    /\ wait_queue' = wait_queue

CompleteUpgrade(t) ==
    /\ pc[t] = "upgrading"
    /\ lock_state.readers = 0
    /\ pc' = [pc EXCEPT ![t] = "writing"]
    /\ lock_state' = [ writer |-> TRUE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0 ]
    /\ wait_queue' = wait_queue

Downgrade(t) ==
    /\ pc[t] = "writing"
    /\ lock_state.writer = TRUE
    /\ lock_state.upreader = FALSE
    /\ lock_state.upgrading = FALSE
    /\ lock_state.readers = 0
    /\ pc' = [pc EXCEPT ![t] = "upreading"]
    /\ lock_state' = [ writer |-> FALSE, upreader |-> TRUE, upgrading |-> FALSE, readers |-> 0 ]
    /\ wait_queue' = wait_queue

(*-- Action to service the wait queue, modeling wakeups --*)

ServiceWaitQueue ==
    /\ Len(wait_queue) > 0
    /\ LET head == Head(wait_queue)
           is_reader_request(thr) == \E op \in {"read", "upread"} : pc[thr] = "waiting" /\ RequestType(thr) = op
           is_writer_request(thr) == pc[thr] = "waiting" /\ RequestType(thr) = "write"
           RequestType(thr) ==
              CHOOSE r \in RequestTypes :
                (r = "read" /\ \/ RequestRead(thr) \/ ReleaseRead(thr))
             \/ (r = "write" /\ \/ RequestWrite(thr) \/ ReleaseWrite(thr) \/ Downgrade(thr) \/ CompleteUpgrade(thr))
             \/ (r = "upread" /\ \/ RequestUpread(thr) \/ ReleaseUpread(thr) \/ StartUpgrade(thr))
    IN
    /\ \/ /\ is_writer_request(head)
          /\ CanAcquireWrite(lock_state)
          /\ pc' = [pc EXCEPT ![head] = "writing"]
          /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
          /\ wait_queue' = Tail(wait_queue)
       \/ /\ is_reader_request(head)
          /\ CanAcquireRead(lock_state)
          /\ LET
                \* Find all consecutive readers at the head of the queue
                readers_to_wake == { wait_queue[i] : i \in 1..Len(wait_queue) }
                is_upreader_present == \E thr \in readers_to_wake : RequestType(thr) = "upread"
                num_upreaders == Cardinality({thr \in readers_to_wake : RequestType(thr) = "upread"})
                
                \* An upreader can be woken if no other upreader is active or will be woken
                CanWakeUpreader(thr) == RequestType(thr) = "upread" /\ lock_state.upreader = FALSE /\ num_upreaders = 1
                
                \* A reader can always be woken if the lock is available for reading
                CanWakeReader(thr) == RequestType(thr) = "read"
                
                \* Determine the group of threads to wake up
                \* A writer or a single upreader stops the reader train
                CanWake(thr) == CanWakeReader(thr) \/ CanWakeUpreader(thr)
                
                \* Find the first waiter that cannot be woken with the head
                first_blocker_idx ==
                    IF \E i \in 1..Len(wait_queue) : ~CanWake(wait_queue[i])
                    THEN CHOOSE i \in 1..Len(wait_queue) : ~CanWake(wait_queue[i]) /\ \A j \in 1..(i-1) : CanWake(wait_queue[j])
                    ELSE Len(wait_queue) + 1
                
                woken_group == { wait_queue[i] : i \in 1..(first_blocker_idx - 1) }
                
                new_pc == [ t \in Threads |->
                              IF t \in woken_group THEN
                                  IF RequestType(t) = "read" THEN "reading"
                                  ELSE "upreading"
                              ELSE pc[t] ]
                
                num_new_readers == Cardinality({t \in woken_group : RequestType(t) = "read"})
                num_new_upreaders == Cardinality({t \in woken_group : RequestType(t) = "upread"})
             IN
             /\ num_new_upreaders <= 1
             /\ pc' = new_pc
             /\ lock_state' = [ lock_state EXCEPT !.readers = @ + num_new_readers,
                                                 !.upreader = (@ \/ (num_new_upreaders > 0)) ]
             /\ wait_queue' = SubSeq(wait_queue, first_blocker_idx, Len(wait_queue))

Next ==
    \/ \E t \in Threads:
        \/ RequestRead(t)
        \/ RequestWrite(t)
        \/ RequestUpread(t)
        \/ ReleaseRead(t)
        \/ ReleaseWrite(t)
        \/ ReleaseUpread(t)
        \/ StartUpgrade(t)
        \/ CompleteUpgrade(t)
        \/ Downgrade(t)
    \/ ServiceWaitQueue
    \/ (* Stuttering step for unchanged vars when no action is enabled *)
       UNCHANGED vars

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

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A t \in Threads : WF_vars(ThreadAction(t))
    /\ WF_vars(ServiceWaitQueue)

====
