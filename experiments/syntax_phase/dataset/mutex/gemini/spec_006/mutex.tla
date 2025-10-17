---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

ASSUME Threads \subseteq Nat

VARIABLES
    lock_held,
    wait_queue,
    critical_section,
    pc

Nil == "Nil"

Vars == << lock_held, wait_queue, critical_section, pc >>

TypeOK ==
    /\ lock_held \in BOOLEAN
    /\ wait_queue \in Seq(Threads)
    /\ critical_section \in Threads \cup {Nil}
    /\ pc \in [Threads -> {"idle", "req_lock", "req_try_lock", "waiting", "in_cs"}]

Init ==
    /\ lock_held = FALSE
    /\ wait_queue = <<>>
    /\ critical_section = Nil
    /\ pc = [t \in Threads |-> "idle"]

RequestLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "req_lock"]
    /\ UNCHANGED << lock_held, wait_queue, critical_section >>

RequestTryLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "req_try_lock"]
    /\ UNCHANGED << lock_held, wait_queue, critical_section >>

ProcessLockRequest(t) ==
    /\ pc[t] = "req_lock"
    /\ IF lock_held = FALSE
       THEN /\ lock_held' = TRUE
            /\ critical_section' = t
            /\ pc' = [pc EXCEPT ![t] = "in_cs"]
            /\ UNCHANGED << wait_queue >>
       ELSE /\ wait_queue' = Append(wait_queue, t)
            /\ pc' = [pc EXCEPT ![t] = "waiting"]
            /\ UNCHANGED << lock_held, critical_section >>

ProcessTryLockRequest(t) ==
    /\ pc[t] = "req_try_lock"
    /\ IF lock_held = FALSE
       THEN /\ lock_held' = TRUE
            /\ critical_section' = t
            /\ pc' = [pc EXCEPT ![t] = "in_cs"]
       ELSE /\ pc' = [pc EXCEPT ![t] = "idle"]
            /\ UNCHANGED << lock_held, critical_section >>
    /\ UNCHANGED << wait_queue >>

Unlock(t) ==
    /\ pc[t] = "in_cs"
    /\ critical_section = t
    /\ lock_held' = FALSE
    /\ critical_section' = Nil
    /\ IF wait_queue /= <<>>
       THEN /\ LET woken_thread == Head(wait_queue)
            IN pc' = [pc EXCEPT ![t] = "idle", !woken_thread = "req_lock"]
            /\ wait_queue' = Tail(wait_queue)
       ELSE /\ pc' = [pc EXCEPT ![t] = "idle"]
            /\ UNCHANGED << wait_queue >>

Next ==
    \E t \in Threads:
        \/ RequestLock(t)
        \/ RequestTryLock(t)
        \/ ProcessLockRequest(t)
        \/ ProcessTryLockRequest(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====