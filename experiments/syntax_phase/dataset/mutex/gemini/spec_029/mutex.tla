---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, None

ASSUME None \notin Threads

VARIABLES is_locked, wait_queue, pc, holder

vars == <<is_locked, wait_queue, pc, holder>>

TypeOK ==
    /\ is_locked \in BOOLEAN
    /\ wait_queue \in Seq(Threads)
    /\ holder \in Threads \cup {None}
    /\ pc \in [Threads -> {"idle", "wants_lock", "wants_trylock", "waiting", "in_cs"}]
    /\ is_locked <=> (holder /= None)
    /\ holder /= None => pc[holder] = "in_cs"
    /\ \A t \in Threads : pc[t] = "in_cs" <=> holder = t
    /\ \A t \in Threads : pc[t] = "waiting" <=> t \in {wait_queue[i] : i \in DOMAIN wait_queue}

Init ==
    /\ is_locked = FALSE
    /\ wait_queue = <<>>
    /\ pc = [t \in Threads |-> "idle"]
    /\ holder = None

RequestLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "wants_lock"]
    /\ UNCHANGED <<is_locked, wait_queue, holder>>

RequestTryLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "wants_trylock"]
    /\ UNCHANGED <<is_locked, wait_queue, holder>>

Acquire(t) ==
    /\ pc[t] \in {"wants_lock", "wants_trylock"}
    /\ \lnot is_locked
    /\ is_locked' = TRUE
    /\ holder' = t
    /\ pc' = [pc EXCEPT ![t] = "in_cs"]
    /\ UNCHANGED <<wait_queue>>

BlockOnLock(t) ==
    /\ pc[t] = "wants_lock"
    /\ is_locked
    /\ pc' = [pc EXCEPT ![t] = "waiting"]
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED <<is_locked, holder>>

FailOnTryLock(t) ==
    /\ pc[t] = "wants_trylock"
    /\ is_locked
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<is_locked, wait_queue, holder>>

Unlock(t) ==
    /\ pc[t] = "in_cs"
    /\ holder = t
    /\ is_locked' = FALSE
    /\ holder' = None
    /\ IF wait_queue = <<>> THEN
        /\ pc' = [pc EXCEPT ![t] = "idle"]
        /\ wait_queue' = wait_queue
    /\ ELSE
        /\ LET woken_thread == Head(wait_queue) IN
           /\ wait_queue' = Tail(wait_queue)
           /\ pc' = [pc EXCEPT ![t] = "idle", ![woken_thread] = "wants_lock"]

Next ==
    \E t \in Threads :
        \/ RequestLock(t)
        \/ RequestTryLock(t)
        \/ Acquire(t)
        \/ BlockOnLock(t)
        \/ FailOnTryLock(t)
        \/ Unlock(t)

Fairness ==
    /\ \A t \in Threads : WF_vars(RequestLock(t))
    /\ \A t \in Threads : WF_vars(RequestTryLock(t))
    /\ \A t \in Threads : WF_vars(Acquire(t))
    /\ \A t \in Threads : WF_vars(BlockOnLock(t))
    /\ \A t \in Threads : WF_vars(FailOnTryLock(t))
    /\ \A t \in Threads : WF_vars(Unlock(t))

Spec == Init /\ [][Next]_vars /\ Fairness

====