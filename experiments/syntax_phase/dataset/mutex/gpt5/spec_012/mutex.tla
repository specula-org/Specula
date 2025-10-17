---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, NoThread

ASSUME NoThread \notin Threads
ASSUME IsFiniteSet(Threads) /\ Threads # {}

Head(s) == s[1]
Tail(s) == SubSeq(s, 2, Len(s))
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

VARIABLES lock, owner, queue, state

TypeOK ==
  /\ lock \in BOOLEAN
  /\ owner \in Threads \cup {NoThread}
  /\ queue \in Seq(Threads)
  /\ \A i,j \in 1..Len(queue): i # j => queue[i] # queue[j]
  /\ state \in [Threads -> {"Running","Waiting","Holding"}]
  /\ { t \in Threads : state[t] = "Waiting" } = { queue[i] : i \in 1..Len(queue) }
  /\ LET holders == { t \in Threads : state[t] = "Holding" } IN
       /\ (lock => holders = {owner})
       /\ (~lock => /\ holders = {} /\ owner = NoThread)

Init ==
  /\ lock = FALSE
  /\ owner = NoThread
  /\ queue = <<>>
  /\ state = [ t \in Threads |-> "Running" ]
  /\ TypeOK

TryLock(t) ==
  /\ t \in Threads
  /\ state[t] = "Running"
  /\ ~lock
  /\ lock' = TRUE
  /\ owner' = t
  /\ queue' = queue
  /\ state' = [state EXCEPT ![t] = "Holding"]

LockAcquire(t) ==
  /\ t \in Threads
  /\ state[t] = "Running"
  /\ ~lock
  /\ lock' = TRUE
  /\ owner' = t
  /\ queue' = queue
  /\ state' = [state EXCEPT ![t] = "Holding"]

LockEnqueue(t) ==
  /\ t \in Threads
  /\ state[t] = "Running"
  /\ lock
  /\ t \notin SeqToSet(queue)
  /\ queue' = Append(queue, t)
  /\ lock' = lock
  /\ owner' = owner
  /\ state' = [state EXCEPT ![t] = "Waiting"]

Unlock_NoWaiters(t) ==
  /\ t \in Threads
  /\ state[t] = "Holding"
  /\ owner = t
  /\ Len(queue) = 0
  /\ lock' = FALSE
  /\ owner' = NoThread
  /\ queue' = queue
  /\ state' = [state EXCEPT ![t] = "Running"]

Unlock_GrantHead(t) ==
  /\ t \in Threads
  /\ state[t] = "Holding"
  /\ owner = t
  /\ Len(queue) > 0
  /\ LET h == Head(queue) IN
       /\ lock' = TRUE
       /\ owner' = h
       /\ queue' = Tail(queue)
       /\ state' = [state EXCEPT ![t] = "Running", ![h] = "Holding"]

Next ==
  ( \E t \in Threads:
      TryLock(t)
      \/ LockAcquire(t)
      \/ LockEnqueue(t)
      \/ Unlock_NoWaiters(t)
      \/ Unlock_GrantHead(t)
  )
  /\ TypeOK'

Vars == << lock, owner, queue, state >>

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====