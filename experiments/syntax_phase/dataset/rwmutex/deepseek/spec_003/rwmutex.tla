---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads

VARIABLES 
    lock_state,
    wait_queue,
    thread_states

vars == <<lock_state, wait_queue, thread_states>>

Init == 
    /\ lock_state = [writer |-> FALSE, upgradeable_reader |-> FALSE, being_upgraded |-> FALSE, readers |-> 0]
    /\ wait_queue = <<>>
    /\ thread_states = [t \in Threads |-> "idle"]

CanReadAcquire == 
    /\ ~lock_state.writer
    /\ ~lock_state.being_upgraded

ReadAcquire(t) ==
    /\ thread_states[t] = "idle"
    /\ CanReadAcquire
    /\ lock_state' = [lock_state EXCEPT !.readers = lock_state.readers + 1]
    /\ thread_states' = [thread_states EXCEPT ![t] = "reading"]
    /\ wait_queue' = wait_queue

CanWriteAcquire ==
    /\ lock_state.readers = 0
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader

WriteAcquire(t) ==
    /\ thread_states[t] = "idle"
    /\ CanWriteAcquire
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
    /\ thread_states' = [thread_states EXCEPT ![t] = "writing"]
    /\ wait_queue' = wait_queue

CanUpreadAcquire ==
    /\ ~lock_state.writer
    /\ ~lock_state.upgradeable_reader

UpreadAcquire(t) ==
    /\ thread_states[t] = "idle"
    /\ CanUpreadAcquire
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = TRUE]
    /\ thread_states' = [thread_states EXCEPT ![t] = "upgrade_reading"]
    /\ wait_queue' = wait_queue

BlockRead(t) ==
    /\ thread_states[t] = "idle"
    /\ ~CanReadAcquire
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting_read"]
    /\ wait_queue' = Append(wait_queue, [type |-> "read", thread |-> t])
    /\ UNCHANGED lock_state

BlockWrite(t) ==
    /\ thread_states[t] = "idle"
    /\ ~CanWriteAcquire
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting_write"]
    /\ wait_queue' = Append(wait_queue, [type |-> "write", thread |-> t])
    /\ UNCHANGED lock_state

BlockUpread(t) ==
    /\ thread_states[t] = "idle"
    /\ ~CanUpreadAcquire
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting_upread"]
    /\ wait_queue' = Append(wait_queue, [type |-> "upread", thread |-> t])
    /\ UNCHANGED lock_state

StartUpgrade(t) ==
    /\ thread_states[t] = "upgrade_reading"
    /\ lock_state' = [lock_state EXCEPT !.being_upgraded = TRUE]
    /\ thread_states' = [thread_states EXCEPT ![t] = "upgrading"]
    /\ wait_queue' = wait_queue

CompleteUpgrade(t) ==
    /\ thread_states[t] = "upgrading"
    /\ lock_state.readers = 0
    /\ lock_state' = [writer |-> TRUE, upgradeable_reader |-> FALSE, being_upgraded |-> FALSE, readers |-> 0]
    /\ thread_states' = [thread_states EXCEPT ![t] = "writing"]
    /\ wait_queue' = wait_queue

Downgrade(t) ==
    /\ thread_states[t] = "writing"
    /\ lock_state' = [writer |-> FALSE, upgradeable_reader |-> TRUE, being_upgraded |-> FALSE, readers |-> 0]
    /\ thread_states' = [thread_states EXCEPT ![t] = "upgrade_reading"]
    /\ wait_queue' = wait_queue

ReadRelease(t) ==
    /\ thread_states[t] = "reading"
    /\ lock_state' = [lock_state EXCEPT !.readers = lock_state.readers - 1]
    /\ thread_states' = [thread_states EXCEPT ![t] = "idle"]
    /\ \/ /\ lock_state.readers > 1
          /\ wait_queue' = wait_queue
       \/ /\ lock_state.readers = 1
          /\ \E w \in {i \in DOMAIN wait_queue: wait_queue[i].type = "read"}:
                wait_queue' = RemoveAt(wait_queue, w)
                /\ thread_states' = [thread_states' EXCEPT ![wait_queue[w].thread] = "idle"]

WriteRelease(t) ==
    /\ thread_states[t] = "writing"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ wait_queue' = <<>>
    /\ thread_states' = [w \in Threads |-> 
        IF \E i \in DOMAIN wait_queue: wait_queue[i].thread = w 
        THEN "idle" 
        ELSE IF w = t THEN "idle" ELSE thread_states[w]]

UpreadRelease(t) ==
    /\ thread_states[t] = "upgrade_reading"
    /\ lock_state' = [lock_state EXCEPT !.upgradeable_reader = FALSE]
    /\ wait_queue' = <<>>
    /\ thread_states' = [w \in Threads |-> 
        IF \E i \in DOMAIN wait_queue: wait_queue[i].thread = w 
        THEN "idle" 
        ELSE IF w = t THEN "idle" ELSE thread_states[w]]

Next == 
    \/ \E t \in Threads : ReadAcquire(t)
    \/ \E t \in Threads : WriteAcquire(t)
    \/ \E t \in Threads : UpreadAcquire(t)
    \/ \E t \in Threads : BlockRead(t)
    \/ \E t \in Threads : BlockWrite(t)
    \/ \E t \in Threads : BlockUpread(t)
    \/ \E t \in Threads : StartUpgrade(t)
    \/ \E t \in Threads : CompleteUpgrade(t)
    \/ \E t \in Threads : Downgrade(t)
    \/ \E t \in Threads : ReadRelease(t)
    \/ \E t \in Threads : WriteRelease(t)
    \/ \E t \in Threads : UpreadRelease(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====