---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Thread, Nil
ASSUME Thread \subseteq {"t1", "t2", "t3"}
ASSUME Nil \notin Thread

VARIABLES lock, queue, pc, holder

vars == <<lock, queue, pc, holder>>

TypeOK ==
    /\ lock \in BOOLEAN
    /\ queue \in Seq(Thread)
    /\ pc \in [Thread -> {"idle", "in_cs", "waiting"}]
    /\ holder \in Thread \cup {Nil}

Init ==
    /\ lock = FALSE
    /\ queue = <<>>
    /\ pc = [t \in Thread |-> "idle"]
    /\ holder = Nil

\* A thread attempts to acquire the lock non-blockingly.
TryLock(t) ==
    /\ pc[t] = "idle"
    /\ IF lock = FALSE THEN  \* Successful compare_exchange
        /\ lock' = TRUE
        /\ holder' = t
        /\ pc' = [pc EXCEPT ![t] = "in_cs"]
        /\ UNCHANGED <<queue>>
    /\ ELSE  \* Failed compare_exchange, returns immediately
        /\ UNCHANGED <<vars>>

\* A thread attempts to acquire the lock blockingly.
Lock(t) ==
    /\ pc[t] = "idle"
    /\ IF lock = FALSE THEN  \* Acquires immediately
        /\ lock' = TRUE
        /\ holder' = t
        /\ pc' = [pc EXCEPT ![t] = "in_cs"]
        /\ UNCHANGED <<queue>>
    /\ ELSE  \* Fails to acquire, blocks and waits
        /\ pc' = [pc EXCEPT ![t] = "waiting"]
        /\ queue' = Append(queue, t)
        /\ UNCHANGED <<lock, holder>>

\* The thread holding the lock releases it.
Unlock(t) ==
    /\ pc[t] = "in_cs"
    /\ holder = t
    /\ IF Len(queue) > 0 THEN  \* Wake one waiting thread
        LET woken_thread == Head(queue) IN
        \* The lock is released and immediately acquired by the woken thread.
        /\ lock' = TRUE
        /\ holder' = woken_thread
        /\ queue' = Tail(queue)
        /\ pc' = [pc EXCEPT ![t] = "idle", ![woken_thread] = "in_cs"]
    /\ ELSE  \* No one is waiting, just release the lock
        /\ lock' = FALSE
        /\ holder' = Nil
        /\ pc' = [pc EXCEPT ![t] = "idle"]
        /\ UNCHANGED <<queue>>

Next ==
    \/ \E t \in Thread: TryLock(t)
    \/ \E t \in Thread: Lock(t)
    \/ \E t \in Thread: Unlock(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====