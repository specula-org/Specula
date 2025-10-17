---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, NoThread
ASSUME NoThread \notin Threads

STATES == {"Idle", "Waiting", "Notified", "Holding"}

VARIABLES lock, owner, queue, state

TypeOK ==
    /\ lock \in BOOLEAN
    /\ owner \in Threads \cup {NoThread}
    /\ queue \in Seq(Threads)
    /\ state \in [Threads -> STATES]
    /\ (lock = TRUE) <=> (owner \in Threads)

Init ==
    /\ lock = FALSE
    /\ owner = NoThread
    /\ queue = <<>>
    /\ state = [t \in Threads |-> "Idle"]

Head(q) == q[1]
Tail(q) == IF Len(q) = 0 THEN <<>> ELSE SubSeq(q, 2, Len(q))
InSeq(q, x) == \E i \in 1..Len(q): q[i] = x
NoNotified == \A t \in Threads: state[t] # "Notified"

TryLockSuccess(t) ==
    /\ t \in Threads
    /\ state[t] = "Idle"
    /\ lock = FALSE
    /\ NoNotified
    /\ lock' = TRUE
    /\ owner' = t
    /\ queue' = queue
    /\ state' = [state EXCEPT ![t] = "Holding"]

TryLockFail(t) ==
    /\ t \in Threads
    /\ state[t] = "Idle"
    /\ lock = TRUE
    /\ UNCHANGED << lock, owner, queue, state >>

LockImmediateAcquire(t) ==
    /\ t \in Threads
    /\ state[t] = "Idle"
    /\ lock = FALSE
    /\ NoNotified
    /\ lock' = TRUE
    /\ owner' = t
    /\ queue' = queue
    /\ state' = [state EXCEPT ![t] = "Holding"]

StartLockEnqueue(t) ==
    /\ t \in Threads
    /\ state[t] = "Idle"
    /\ lock = TRUE
    /\ ~InSeq(queue, t)
    /\ lock' = lock
    /\ owner' = owner
    /\ queue' = Append(queue, t)
    /\ state' = [state EXCEPT ![t] = "Waiting"]

NotifiedAcquire(t) ==
    /\ t \in Threads
    /\ state[t] = "Notified"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ owner' = t
    /\ queue' = queue
    /\ state' = [state EXCEPT ![t] = "Holding"]

Unlock(t) ==
    /\ t \in Threads
    /\ state[t] = "Holding"
    /\ owner = t
    /\ lock' = FALSE
    /\ owner' = NoThread
    /\ IF Len(queue) = 0
       THEN /\ queue' = queue
            /\ state' = [state EXCEPT ![t] = "Idle"]
       ELSE /\ queue' = Tail(queue)
            /\ state' = [state EXCEPT ![t] = "Idle", ![Head(queue)] = "Notified"]

Next ==
    \E t \in Threads:
        TryLockSuccess(t)
        \/ TryLockFail(t)
        \/ LockImmediateAcquire(t)
        \/ StartLockEnqueue(t)
        \/ NotifiedAcquire(t)
        \/ Unlock(t)

Vars == << lock, owner, queue, state >>

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====