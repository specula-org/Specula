
---- MODULE mutex ----
EXTENDS Sequences, Naturals, FiniteSets, TLC

CONSTANTS Threads

VARIABLES pc, lock, queue, mode

TypeOK == 
    /\ lock \in BOOLEAN
    /\ queue \in Seq(Threads)
    /\ pc \in [Threads -> {"start", "trying", "waiting", "critical", "done", "try_fail"}]
    /\ mode \in [Threads -> {"none", "blocking", "nonblocking"}]

Init == 
    /\ lock = FALSE
    /\ queue = <<>>
    /\ pc = [t \in Threads |-> "start"]
    /\ mode = [t \in Threads |-> "none"]

Lock(t) == 
    /\ pc[t] \in {"start", "try_fail"}
    /\ pc' = [pc EXCEPT ![t] = "trying"]
    /\ mode' = [mode EXCEPT ![t] = "blocking"]
    /\ UNCHANGED <<lock, queue>>

TryLock(t) == 
    /\ pc[t] \in {"start", "try_fail"}
    /\ pc' = [pc EXCEPT ![t] = "trying"]
    /\ mode' = [mode EXCEPT ![t] = "nonblocking"]
    /\ UNCHANGED <<lock, queue>>

Acquire(t) == 
    /\ pc[t] = "trying"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ pc' = [pc EXCEPT ![t] = "critical"]
    /\ mode' = [mode EXCEPT ![t] = "none"]
    /\ UNCHANGED <<queue>>

Fail(t) == 
    /\ pc[t] = "trying"
    /\ lock = TRUE
    /\ IF mode[t] = "blocking"
        THEN /\ pc' = [pc EXCEPT ![t] = "waiting"]
             /\ queue' = Append(queue, t)
             /\ mode' = mode
        ELSE /\ pc' = [pc EXCEPT ![t] = "try_fail"]
             /\ mode' = [mode EXCEPT ![t] = "none"]
    /\ lock' = lock

Unlock(t) == 
    /\ pc[t] = "critical"
    /\ lock' = FALSE
    /\ LET pc1 == [pc EXCEPT ![t] = "done"]
       IN IF queue /= <<>>
            THEN LET u == Head(queue) IN
                 /\ pc' = [pc1 EXCEPT ![u] = "trying"]
                 /\ queue' = Tail(queue)
            ELSE /\ pc' = pc1
                 /\ queue' = queue
    /\ mode' = mode

Leave(t) == 
    /\ pc[t] = "try_fail"
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED <<lock, queue, mode>>

Reset(t) == 
    /\ pc[t] = "done"
    /\ pc' = [pc EXCEPT ![t] = "start"]
    /\ UNCHANGED <<lock, queue, mode>>

Next == 
    \E t \in Threads: 
        Lock(t) \/ TryLock(t) \/ Acquire(t) \/ Fail(t) \/ Unlock(t) \/ Leave(t) \/ Reset(t)

Vars == <<pc, lock, queue, mode>>

WF_Vars(A) == WF_<<pc, lock, queue, mode>>(A)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====