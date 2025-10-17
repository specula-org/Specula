---- MODULE mutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANT THREADS

VARIABLES lock, queue, guard, waiting, notified

Head(s) == s[1]
Tail(s) == IF Len(s) = 0 THEN << >> ELSE SubSeq(s, 2, Len(s))

InSeq(q, x) == \E i \in 1..Len(q): q[i] = x

TypeOK ==
  /\ lock \in BOOLEAN
  /\ queue \in Seq(THREADS)
  /\ guard \in [THREADS -> BOOLEAN]
  /\ waiting \in [THREADS -> BOOLEAN]
  /\ notified \in [THREADS -> BOOLEAN]

Init ==
  /\ TypeOK
  /\ lock = FALSE
  /\ queue = << >>
  /\ guard = [t \in THREADS |-> FALSE]
  /\ waiting = [t \in THREADS |-> FALSE]
  /\ notified = [t \in THREADS |-> FALSE]

TryLock(t) ==
  /\ t \in THREADS
  /\ ~guard[t]
  /\ ~waiting[t]
  /\ ~notified[t]
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ guard' = [guard EXCEPT ![t] = TRUE]
  /\ UNCHANGED << queue, waiting, notified >>

Lock_Block(t) ==
  /\ t \in THREADS
  /\ ~guard[t]
  /\ ~waiting[t]
  /\ ~notified[t]
  /\ lock = TRUE
  /\ ~InSeq(queue, t)
  /\ queue' = queue \o << t >>
  /\ waiting' = [waiting EXCEPT ![t] = TRUE]
  /\ UNCHANGED << lock, guard, notified >>

WokenAcquire(t) ==
  /\ t \in THREADS
  /\ notified[t]
  /\ ~guard[t]
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ guard' = [guard EXCEPT ![t] = TRUE]
  /\ notified' = [notified EXCEPT ![t] = FALSE]
  /\ UNCHANGED << queue, waiting >>

WokenRequeue(t) ==
  /\ t \in THREADS
  /\ notified[t]
  /\ ~guard[t]
  /\ lock = TRUE
  /\ ~InSeq(queue, t)
  /\ notified' = [notified EXCEPT ![t] = FALSE]
  /\ queue' = queue \o << t >>
  /\ waiting' = [waiting EXCEPT ![t] = TRUE]
  /\ UNCHANGED << lock, guard >>

Unlock(t) ==
  /\ t \in THREADS
  /\ guard[t]
  /\ lock = TRUE
  /\ lock' = FALSE
  /\ guard' = [guard EXCEPT ![t] = FALSE]
  /\ IF Len(queue) = 0
     THEN /\ queue' = queue
          /\ waiting' = waiting
          /\ notified' = notified
     ELSE
       LET w == Head(queue) IN
         /\ queue' = Tail(queue)
         /\ waiting' = [waiting EXCEPT ![w] = FALSE]
         /\ notified' = [notified EXCEPT ![w] = TRUE]

Next ==
  \E t \in THREADS:
    TryLock(t)
    \/ Lock_Block(t)
    \/ WokenAcquire(t)
    \/ WokenRequeue(t)
    \/ Unlock(t)

Vars == << lock, queue, guard, waiting, notified >>

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====