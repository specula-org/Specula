---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads
ASSUME Threads /= {}

VARIABLES locked, owner, wait_queue, thread_state

vars == <<locked, owner, wait_queue, thread_state>>

ThreadStates == {"idle", "holding", "waiting", "woken"}
None == CHOOSE v : v \notin Threads

TypeOK ==
    /\ locked \in BOOLEAN
    /\ owner \in Threads \cup {None}
    /\ wait_queue \in Seq(Threads)
    /\ thread_state \in [Threads -> ThreadStates]
    /\ (locked <=> owner /= None)
    /\ (\A t \in Threads: thread_state[t] = "holding" <=> owner = t)
    /\ IsAFcn(thread_state)
    /\ DOMAIN thread_state = Threads

Init ==
    /\ locked = FALSE
    /\ owner = None
    /\ wait_queue = <<>>
    /\ thread_state = [t \in Threads |-> "idle"]

Acquire(t) ==
    /\ thread_state[t] \in {"idle", "woken"}
    /\ \lnot locked
    /\ locked' = TRUE
    /\ owner' = t
    /\ thread_state' = [thread_state EXCEPT ![t] = "holding"]
    /\ UNCHANGED <<wait_queue>>

TryLockFail(t) ==
    /\ thread_state[t] = "idle"
    /\ locked
    /\ UNCHANGED vars

Block(t) ==
    /\ thread_state[t] = "idle"
    /\ locked
    /\ wait_queue' = Append(wait_queue, t)
    /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
    /\ UNCHANGED <<locked, owner>>

Unlock(t) ==
    /\ thread_state[t] = "holding"
    /\ locked' = FALSE
    /\ owner' = None
    /\ IF Len(wait_queue) > 0 THEN
        LET woken_thread == Head(wait_queue) IN
        /\ wait_queue' = Tail(wait_queue)
        /\ thread_state' = [thread_state EXCEPT ![t] = "idle", ![woken_thread] = "woken"]
    ELSE
        /\ wait_queue' = wait_queue
        /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]

Next ==
    \E t \in Threads:
        \/ Acquire(t)
        \/ TryLockFail(t)
        \/ Block(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====