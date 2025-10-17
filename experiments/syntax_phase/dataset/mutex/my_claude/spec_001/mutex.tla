---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES 
    lock_state,
    waiting_threads,
    thread_states,
    guards

vars == <<lock_state, waiting_threads, thread_states, guards>>

ThreadStates == {"running", "waiting"}
LockStates == {"unlocked", "reader_locked", "writer_locked", "upgradeable_locked", "being_upgraded"}
GuardTypes == {"read", "write", "upgradeable"}

TypeOK ==
    /\ lock_state \in [state: LockStates, reader_count: Nat]
    /\ waiting_threads \in Seq(Threads)
    /\ thread_states \in [Threads -> ThreadStates]
    /\ guards \in SUBSET [thread: Threads, type: GuardTypes]

Init ==
    /\ lock_state = [state |-> "unlocked", reader_count |-> 0]
    /\ waiting_threads = <<>>
    /\ thread_states = [t \in Threads |-> "running"]
    /\ guards = {}

TryRead(t) ==
    /\ thread_states[t] = "running"
    /\ lock_state.state \notin {"writer_locked", "being_upgraded"}
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ + 1, !.state = "reader_locked"]
    /\ guards' = guards \union {[thread |-> t, type |-> "read"]}
    /\ UNCHANGED <<waiting_threads, thread_states>>

TryWrite(t) ==
    /\ thread_states[t] = "running"
    /\ lock_state.state = "unlocked"
    /\ lock_state.reader_count = 0
    /\ lock_state' = [state |-> "writer_locked", reader_count |-> 0]
    /\ guards' = guards \union {[thread |-> t, type |-> "write"]}
    /\ UNCHANGED <<waiting_threads, thread_states>>

TryUpread(t) ==
    /\ thread_states[t] = "running"
    /\ lock_state.state \notin {"writer_locked", "upgradeable_locked"}
    /\ lock_state' = [lock_state EXCEPT !.state = "upgradeable_locked"]
    /\ guards' = guards \union {[thread |-> t, type |-> "upgradeable"]}
    /\ UNCHANGED <<waiting_threads, thread_states>>

Read(t) ==
    /\ thread_states[t] = "running"
    /\ lock_state.state \in {"writer_locked", "being_upgraded"}
    /\ waiting_threads' = Append(waiting_threads, t)
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<lock_state, guards>>

Write(t) ==
    /\ thread_states[t] = "running"
    /\ \/ lock_state.state # "unlocked"
       \/ lock_state.reader_count > 0
    /\ waiting_threads' = Append(waiting_threads, t)
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<lock_state, guards>>

Upread(t) ==
    /\ thread_states[t] = "running"
    /\ lock_state.state \in {"writer_locked", "upgradeable_locked"}
    /\ waiting_threads' = Append(waiting_threads, t)
    /\ thread_states' = [thread_states EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<lock_state, guards>>

DropReadGuard(t) ==
    /\ [thread |-> t, type |-> "read"] \in guards
    /\ guards' = guards \ {[thread |-> t, type |-> "read"]}
    /\ lock_state' = [lock_state EXCEPT !.reader_count = @ - 1,
                      !.state = IF @ - 1 = 0 THEN "unlocked" ELSE "reader_locked"]
    /\ IF lock_state'.reader_count = 0 /\ Len(waiting_threads) > 0
       THEN /\ thread_states' = [thread_states EXCEPT ![Head(waiting_threads)] = "running"]
            /\ waiting_threads' = Tail(waiting_threads)
       ELSE UNCHANGED <<waiting_threads, thread_states>>

DropWriteGuard(t) ==
    /\ [thread |-> t, type |-> "write"] \in guards
    /\ guards' = guards \ {[thread |-> t, type |-> "write"]}
    /\ lock_state' = [state |-> "unlocked", reader_count |-> 0]
    /\ IF Len(waiting_threads) > 0
       THEN /\ thread_states' = [thread_states EXCEPT 
                                 ![waiting_threads[i]] = "running" : i \in 1..Len(waiting_threads)]
            /\ waiting_threads' = <<>>
       ELSE UNCHANGED <<waiting_threads, thread_states>>

DropUpgradeableGuard(t) ==
    /\ [thread |-> t, type |-> "upgradeable"] \in guards
    /\ guards' = guards \ {[thread |-> t, type |-> "upgradeable"]}
    /\ lock_state' = IF lock_state.reader_count > 0 
                     THEN [state |-> "reader_locked", reader_count |-> lock_state.reader_count]
                     ELSE [state |-> "unlocked", reader_count |-> 0]
    /\ IF Len(waiting_threads) > 0
       THEN /\ thread_states' = [thread_states EXCEPT 
                                 ![waiting_threads[i]] = "running" : i \in 1..Len(waiting_threads)]
            /\ waiting_threads' = <<>>
       ELSE UNCHANGED <<waiting_threads, thread_states>>

Upgrade(t) ==
    /\ [thread |-> t, type |-> "upgradeable"] \in guards
    /\ lock_state.state = "upgradeable_locked"
    /\ lock_state.reader_count = 0
    /\ lock_state' = [state |-> "writer_locked", reader_count |-> 0]
    /\ guards' = (guards \ {[thread |-> t, type |-> "upgradeable"]}) \union {[thread |-> t, type |-> "write"]}
    /\ UNCHANGED <<waiting_threads, thread_states>>

BeginUpgrade(t) ==
    /\ [thread |-> t, type |-> "upgradeable"] \in guards
    /\ lock_state.state = "upgradeable_locked"
    /\ lock_state.reader_count > 0
    /\ lock_state' = [lock_state EXCEPT !.state = "being_upgraded"]
    /\ UNCHANGED <<waiting_threads, thread_states, guards>>

WakeWaitingThread ==
    /\ Len(waiting_threads) > 0
    /\ \E t \in {Head(waiting_threads)} :
        /\ thread_states[t] = "waiting"
        /\ \/ /\ lock_state.state \notin {"writer_locked", "being_upgraded"}
              /\ TryRead(t)
           \/ /\ lock_state.state = "unlocked"
              /\ lock_state.reader_count = 0
              /\ TryWrite(t)
           \/ /\ lock_state.state \notin {"writer_locked", "upgradeable_locked"}
              /\ TryUpread(t)
        /\ waiting_threads' = Tail(waiting_threads)
        /\ thread_states' = [thread_states EXCEPT ![t] = "running"]

Next ==
    \/ \E t \in Threads : TryRead(t)
    \/ \E t \in Threads : TryWrite(t)
    \/ \E t \in Threads : TryUpread(t)
    \/ \E t \in Threads : Read(t)
    \/ \E t \in Threads : Write(t)
    \/ \E t \in Threads : Upread(t)
    \/ \E t \in Threads : DropReadGuard(t)
    \/ \E t \in Threads : DropWriteGuard(t)
    \/ \E t \in Threads : DropUpgradeableGuard(t)
    \/ \E t \in Threads : Upgrade(t)
    \/ \E t \in Threads : BeginUpgrade(t)
    \/ WakeWaitingThread

Spec == Init /\ [][Next]_vars /\ WF_vars(WakeWaitingThread) /\ WF_vars(\E t \in Threads : DropReadGuard(t) \/ DropWriteGuard(t) \/ DropUpgradeableGuard(t))

====