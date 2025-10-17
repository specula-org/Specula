---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, MaxReaders

VARIABLES 
    lock_state,
    wait_queue,
    thread_state,
    guards

Vars == <<lock_state, wait_queue, thread_state, guards>>

ThreadStates == {"running", "waiting", "terminated"}
GuardTypes == {"none", "read", "write", "upread"}

TypeOK == 
    /\ lock_state \in [readers: 0..MaxReaders, writer: BOOLEAN, upread: BOOLEAN, upgrading: BOOLEAN]
    /\ wait_queue \in Seq(Threads)
    /\ thread_state \in [Threads -> ThreadStates]
    /\ guards \in [Threads -> GuardTypes]

Init ==
    /\ lock_state = [readers |-> 0, writer |-> FALSE, upread |-> FALSE, upgrading |-> FALSE]
    /\ wait_queue = <<>>
    /\ thread_state = [t \in Threads |-> "running"]
    /\ guards = [t \in Threads |-> "none"]

CanRead == 
    /\ ~lock_state.writer
    /\ ~lock_state.upgrading
    /\ lock_state.readers < MaxReaders

CanWrite == 
    /\ lock_state.readers = 0
    /\ ~lock_state.writer
    /\ ~lock_state.upread

CanUpread ==
    /\ ~lock_state.writer
    /\ ~lock_state.upread

TryRead(t) ==
    /\ thread_state[t] = "running"
    /\ guards[t] = "none"
    /\ CanRead
    /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
    /\ guards' = [guards EXCEPT ![t] = "read"]
    /\ UNCHANGED <<wait_queue, thread_state>>

TryWrite(t) ==
    /\ thread_state[t] = "running"
    /\ guards[t] = "none"
    /\ CanWrite
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
    /\ guards' = [guards EXCEPT ![t] = "write"]
    /\ UNCHANGED <<wait_queue, thread_state>>

TryUpread(t) ==
    /\ thread_state[t] = "running"
    /\ guards[t] = "none"
    /\ CanUpread
    /\ lock_state' = [lock_state EXCEPT !.upread = TRUE]
    /\ guards' = [guards EXCEPT ![t] = "upread"]
    /\ UNCHANGED <<wait_queue, thread_state>>

BlockingRead(t) ==
    /\ thread_state[t] = "running"
    /\ guards[t] = "none"
    /\ ~CanRead
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<lock_state, guards>>

BlockingWrite(t) ==
    /\ thread_state[t] = "running"
    /\ guards[t] = "none"
    /\ ~CanWrite
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<lock_state, guards>>

BlockingUpread(t) ==
    /\ thread_state[t] = "running"
    /\ guards[t] = "none"
    /\ ~CanUpread
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<lock_state, guards>>

UnlockRead(t) ==
    /\ guards[t] = "read"
    /\ lock_state' = [lock_state EXCEPT !.readers = @ - 1]
    /\ guards' = [guards EXCEPT ![t] = "none"]
    /\ IF lock_state'.readers = 0 /\ wait_queue # <<>>
       THEN /\ thread_state' = [thread_state EXCEPT ![Head(wait_queue)] = "running"]
            /\ wait_queue' = Tail(wait_queue)
       ELSE UNCHANGED <<wait_queue, thread_state>>

UnlockWrite(t) ==
    /\ guards[t] = "write"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ guards' = [guards EXCEPT ![t] = "none"]
    /\ IF wait_queue # <<>>
       THEN /\ \E i \in 1..Len(wait_queue) : 
                thread_state' = [thread_state EXCEPT ![wait_queue[i]] = "running"]
            /\ wait_queue' = <<>>
       ELSE UNCHANGED <<wait_queue, thread_state>>

UnlockUpread(t) ==
    /\ guards[t] = "upread"
    /\ lock_state' = [lock_state EXCEPT !.upread = FALSE]
    /\ guards' = [guards EXCEPT ![t] = "none"]
    /\ IF wait_queue # <<>>
       THEN /\ \E i \in 1..Len(wait_queue) : 
                thread_state' = [thread_state EXCEPT ![wait_queue[i]] = "running"]
            /\ wait_queue' = <<>>
       ELSE UNCHANGED <<wait_queue, thread_state>>

TryUpgrade(t) ==
    /\ guards[t] = "upread"
    /\ lock_state.readers = 0
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.upread = FALSE]
    /\ guards' = [guards EXCEPT ![t] = "write"]
    /\ UNCHANGED <<wait_queue, thread_state>>

StartUpgrade(t) ==
    /\ guards[t] = "upread"
    /\ lock_state.readers > 0
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]
    /\ UNCHANGED <<wait_queue, thread_state, guards>>

WakeWaitingThread ==
    /\ wait_queue # <<>>
    /\ LET t == Head(wait_queue)
       IN /\ thread_state[t] = "waiting"
          /\ \/ /\ CanRead
                /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
                /\ guards' = [guards EXCEPT ![t] = "read"]
             \/ /\ CanWrite
                /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
                /\ guards' = [guards EXCEPT ![t] = "write"]
             \/ /\ CanUpread
                /\ lock_state' = [lock_state EXCEPT !.upread = TRUE]
                /\ guards' = [guards EXCEPT ![t] = "upread"]
          /\ thread_state' = [thread_state EXCEPT ![t] = "running"]
          /\ wait_queue' = Tail(wait_queue)

Next ==
    \/ \E t \in Threads : TryRead(t)
    \/ \E t \in Threads : TryWrite(t)
    \/ \E t \in Threads : TryUpread(t)
    \/ \E t \in Threads : BlockingRead(t)
    \/ \E t \in Threads : BlockingWrite(t)
    \/ \E t \in Threads : BlockingUpread(t)
    \/ \E t \in Threads : UnlockRead(t)
    \/ \E t \in Threads : UnlockWrite(t)
    \/ \E t \in Threads : UnlockUpread(t)
    \/ \E t \in Threads : TryUpgrade(t)
    \/ \E t \in Threads : StartUpgrade(t)
    \/ WakeWaitingThread

Spec == Init /\ [][Next]_Vars /\ WF_Vars(WakeWaitingThread) /\ \A t \in Threads : WF_Vars(UnlockRead(t)) /\ \A t \in Threads : WF_Vars(UnlockWrite(t)) /\ \A t \in Threads : WF_Vars(UnlockUpread(t))

====