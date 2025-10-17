---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS THREADS

VARIABLES lock, owner, queue, woken

SeqToSet(s) == { s[i] : i \in DOMAIN s }

TypeOK ==
  /\ lock \in BOOLEAN
  /\ owner \in THREADS \cup {"Nil"}
  /\ queue \in Seq(THREADS)
  /\ \A i, j \in DOMAIN queue : i # j => queue[i] # queue[j]
  /\ woken \subseteq THREADS
  /\ woken \cap SeqToSet(queue) = {}

Init ==
  /\ lock = FALSE
  /\ owner = "Nil"
  /\ queue = << >>
  /\ woken = {}

TryLockAcquire(t) ==
  /\ t \in THREADS
  /\ ~lock
  /\ owner = "Nil"
  /\ t \notin SeqToSet(queue)
  /\ t \notin woken
  /\ lock' = TRUE
  /\ owner' = t
  /\ queue' = queue
  /\ woken' = woken

LockAcquire(t) ==
  /\ t \in THREADS
  /\ ~lock
  /\ owner = "Nil"
  /\ t \notin SeqToSet(queue)
  /\ t \notin woken
  /\ lock' = TRUE
  /\ owner' = t
  /\ queue' = queue
  /\ woken' = woken

LockEnqueue(t) ==
  /\ t \in THREADS
  /\ lock = TRUE
  /\ t # owner
  /\ t \notin SeqToSet(queue)
  /\ t \notin woken
  /\ lock' = lock
  /\ owner' = owner
  /\ queue' = Append(queue, t)
  /\ woken' = woken

RetestAcquire(t) ==
  /\ t \in THREADS
  /\ t \in woken
  /\ ~lock
  /\ owner = "Nil"
  /\ lock' = TRUE
  /\ owner' = t
  /\ queue' = queue
  /\ woken' = woken \ { t }

RetestRequeue(t) ==
  /\ t \in THREADS
  /\ t \in woken
  /\ lock = TRUE
  /\ t # owner
  /\ lock' = lock
  /\ owner' = owner
  /\ queue' = Append(queue, t)
  /\ woken' = woken \ { t }

Unlock(t) ==
  /\ t \in THREADS
  /\ owner = t
  /\ lock = TRUE
  /\ lock' = FALSE
  /\ owner' = "Nil"
  /\ IF Len(queue) = 0 THEN
       /\ queue' = queue
       /\ woken' = woken
     ELSE
       LET u == Head(queue) IN
         /\ queue' = Tail(queue)
         /\ woken' = woken \cup { u }

Next ==
  \E t \in THREADS :
       TryLockAcquire(t)
    \/ LockAcquire(t)
    \/ LockEnqueue(t)
    \/ RetestAcquire(t)
    \/ RetestRequeue(t)
    \/ Unlock(t)

Vars == << lock, owner, queue, woken >>

Spec ==
  Init /\ TypeOK /\ [][Next]_Vars
  /\ \A t \in THREADS : WF_Vars(TryLockAcquire(t))
  /\ \A t \in THREADS : WF_Vars(LockAcquire(t))
  /\ \A t \in THREADS : WF_Vars(RetestAcquire(t))
  /\ \A t \in THREADS : WF_Vars(Unlock(t))

====