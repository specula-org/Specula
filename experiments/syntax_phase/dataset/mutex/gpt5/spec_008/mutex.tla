---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES lock, queue, st

Vars == << lock, queue, st >>

InQ(q, t) == ∃ i \in 1..Len(q): q[i] = t
Head(q) == q[1]
Tail(q) == IF Len(q) <= 1 THEN << >> ELSE SubSeq(q, 2, Len(q))

TypeOK ==
  /\ lock \in BOOLEAN
  /\ queue \in Seq(Threads)
  /\ st \in [Threads -> {"Idle", "Waiting", "Woken", "Holding"}]

Init ==
  /\ lock = FALSE
  /\ queue = << >>
  /\ st = [t \in Threads |-> "Idle"]

TryLock(t) ==
  /\ t \in Threads
  /\ st[t] = "Idle"
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ st' = [st EXCEPT ![t] = "Holding"]
  /\ UNCHANGED queue

Lock_AcquireImmediate(t) ==
  /\ t \in Threads
  /\ st[t] = "Idle"
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ st' = [st EXCEPT ![t] = "Holding"]
  /\ UNCHANGED queue

Lock_Enqueue(t) ==
  /\ t \in Threads
  /\ st[t] = "Idle"
  /\ lock = TRUE
  /\ ~InQ(queue, t)
  /\ queue' = Append(queue, t)
  /\ st' = [st EXCEPT ![t] = "Waiting"]
  /\ UNCHANGED lock

Woken_Acquire(t) ==
  /\ t \in Threads
  /\ st[t] = "Woken"
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ st' = [st EXCEPT ![t] = "Holding"]
  /\ UNCHANGED queue

Woken_Requeue(t) ==
  /\ t \in Threads
  /\ st[t] = "Woken"
  /\ lock = TRUE
  /\ ~InQ(queue, t)
  /\ queue' = Append(queue, t)
  /\ st' = [st EXCEPT ![t] = "Waiting"]
  /\ UNCHANGED lock

Unlock(t) ==
  /\ t \in Threads
  /\ st[t] = "Holding"
  /\ lock' = FALSE
  /\ IF Len(queue) = 0 THEN
       /\ queue' = queue
       /\ st' = [st EXCEPT ![t] = "Idle"]
     ELSE
       /\ LET u == Head(queue) IN
            /\ queue' = Tail(queue)
            /\ st' = [st EXCEPT ![t] = "Idle", ![u] = "Woken"]

Next ==
  \E t \in Threads:
    TryLock(t)
    \/ Lock_AcquireImmediate(t)
    \/ Lock_Enqueue(t)
    \/ Woken_Acquire(t)
    \/ Woken_Requeue(t)
    \/ Unlock(t)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====