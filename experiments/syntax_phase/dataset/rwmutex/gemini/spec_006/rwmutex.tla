---- MODULE raftkvs ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads

VARIABLES lock_state, process_state, wait_queue

vars == <<lock_state, process_state, wait_queue>>

TypeOK ==
    /\ lock_state \in [ writer: BOOLEAN, upgradable: BOOLEAN, upgrading: BOOLEAN, readers: Nat ]
    /\ process_state \in [ Threads -> {"idle", "waiting", "reading", "writing", "upgradable_reading", "upgrading"} ]
    /\ wait_queue \in Seq(Threads)

Init ==
    /\ lock_state = [ writer |-> FALSE, upgradable |-> FALSE, upgrading |-> FALSE, readers |-> 0 ]
    /\ process_state = [ t \in Threads |-> "idle" ]
    /\ wait_queue = <<>>

\* A thread attempts to acquire a read lock.
\* If successful, it becomes a reader.
\* If not, it is enqueued and waits.
RequestRead(t) ==
    /\ process_state[t] = "idle"
    /\ IF ~lock_state["writer"] /\ ~lock_state["upgrading"]
       THEN /\ lock_state' = [lock_state EXCEPT !["readers"] = @ + 1]
            /\ process_state' = [process_state EXCEPT ![t] = "reading"]
            /\ UNCHANGED <<wait_queue>>
       ELSE /\ process_state' = [process_state EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED <<lock_state>>

\* A thread releases a read lock.
\* If it is the last reader, one waiting thread is woken up.
ReleaseRead(t) ==
    /\ process_state[t] = "reading"
    /\ lock_state' = [lock_state EXCEPT !["readers"] = @ - 1]
    /\ IF lock_state["readers"] = 1 /\ Len(wait_queue) > 0
       THEN LET woken_t == Head(wait_queue)
            IN  /\ process_state' = [process_state EXCEPT ![t] = "idle", ![woken_t] = "idle"]
                /\ wait_queue' = Tail(wait_queue)
       ELSE /\ process_state' = [process_state EXCEPT ![t] = "idle"]
            /\ UNCHANGED <<wait_queue>>

\* A thread attempts to acquire a write lock.
\* If successful, it becomes the writer.
\* If not, it is enqueued and waits.
RequestWrite(t) ==
    /\ process_state[t] = "idle"
    /\ IF ~lock_state["writer"] /\ ~lock_state["upgradable"] /\ lock_state["readers"] = 0
       THEN /\ lock_state' = [lock_state EXCEPT !["writer"] = TRUE]
            /\ process_state' = [process_state EXCEPT ![t] = "writing"]
            /\ UNCHANGED <<wait_queue>>
       ELSE /\ process_state' = [process_state EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED <<lock_state>>

\* A thread releases a write lock.
\* All waiting threads are woken up.
ReleaseWrite(t) ==
    /\ process_state[t] = "writing"
    /\ lock_state' = [lock_state EXCEPT !["writer"] = FALSE]
    /\ LET WokenThreads == {wait_queue[i] : i \in 1..Len(wait_queue)}
       IN  process_state' = [p \in Threads |-> IF p = t THEN "idle" ELSE IF p \in WokenThreads THEN "idle" ELSE process_state[p]]
    /\ wait_queue' = <<>>

\* A thread attempts to acquire an upgradeable read lock.
\* If successful, it becomes the upgradeable reader.
\* If not, it is enqueued and waits.
RequestUpgradableRead(t) ==
    /\ process_state[t] = "idle"
    /\ IF ~lock_state["writer"] /\ ~lock_state["upgradable"]
       THEN /\ lock_state' = [lock_state EXCEPT !["upgradable"] = TRUE]
            /\ process_state' = [process_state EXCEPT ![t] = "upgradable_reading"]
            /\ UNCHANGED <<wait_queue>>
       ELSE /\ process_state' = [process_state EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED <<lock_state>>

\* A thread releases an upgradeable read lock.
\* If there are no other readers, all waiting threads are woken up.
ReleaseUpgradableRead(t) ==
    /\ process_state[t] = "upgradable_reading"
    /\ lock_state' = [lock_state EXCEPT !["upgradable"] = FALSE]
    /\ IF lock_state["readers"] = 0
       THEN LET WokenThreads == {wait_queue[i] : i \in 1..Len(wait_queue)}
            IN  /\ process_state' = [p \in Threads |-> IF p = t THEN "idle" ELSE IF p \in WokenThreads THEN "idle" ELSE process_state[p]]
                /\ wait_queue' = <<>>
       ELSE /\ process_state' = [process_state EXCEPT ![t] = "idle"]
            /\ UNCHANGED <<wait_queue>>

\* An upgradeable reader starts the upgrade process.
\* This blocks new readers from acquiring the lock.
StartUpgrade(t) ==
    /\ process_state[t] = "upgradable_reading"
    /\ lock_state' = [lock_state EXCEPT !["upgrading"] = TRUE]
    /\ process_state' = [process_state EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED <<wait_queue>>

\* An upgrading thread completes the upgrade to a write lock.
\* This can only happen when all other readers have released their locks.
CompleteUpgrade(t) ==
    /\ process_state[t] = "upgrading"
    /\ lock_state["readers"] = 0
    /\ lock_state' = [ writer |-> TRUE, upgradable |-> FALSE,
                      upgrading |-> FALSE, readers |-> lock_state["readers"] ]
    /\ process_state' = [process_state EXCEPT ![t] = "writing"]
    /\ UNCHANGED <<wait_queue>>

\* A writer downgrades its lock to an upgradeable read lock.
Downgrade(t) ==
    /\ process_state[t] = "writing"
    /\ lock_state' = [lock_state EXCEPT !["writer"] = FALSE, !["upgradable"] = TRUE]
    /\ process_state' = [process_state EXCEPT ![t] = "upgradable_reading"]
    /\ UNCHANGED <<wait_queue>>

Next ==
    \/ \E t \in Threads:
        \/ RequestRead(t)
        \/ ReleaseRead(t)
        \/ RequestWrite(t)
        \/ ReleaseWrite(t)
        \/ RequestUpgradableRead(t)
        \/ ReleaseUpgradableRead(t)
        \/ StartUpgrade(t)
        \/ CompleteUpgrade(t)
        \/ Downgrade(t)

Fairness ==
    /\ \A t \in Threads: WF_vars(ReleaseRead(t))
    /\ \A t \in Threads: WF_vars(ReleaseWrite(t))
    /\ \A t \in Threads: WF_vars(ReleaseUpgradableRead(t))
    /\ \A t \in Threads: WF_vars(StartUpgrade(t))
    /\ \A t \in Threads: WF_vars(CompleteUpgrade(t))
    /\ \A t \in Threads: WF_vars(Downgrade(t))

Spec == Init /\ [][Next]_vars /\ Fairness

====
```