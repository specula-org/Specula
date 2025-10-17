
---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads, NoThread
ASSUME NoThread \notin Threads
VARIABLES lock, owner, waitQueue, pc

Vars == <<lock, owner, waitQueue, pc>>

TypeOK == 
  /\ lock \in BOOLEAN
  /\ owner \in Threads \cup {NoThread}
  /\ waitQueue \in Seq(Threads)
  /\ pc \in [Threads -> {"idle", "lock_attempt", "try_attempt", "waiting", "in_cs"}]

Init == 
  /\ lock = FALSE
  /\ owner = NoThread
  /\ waitQueue = <<>>
  /\ pc = [t \in Threads |-> "idle"]

StartLock(t) == 
  /\ pc[t] = "idle"
  /\ pc' = [pc EXCEPT ![t] = "lock_attempt"]
  /\ UNCHANGED <<lock, owner, waitQueue>>

StartTryLock(t) == 
  /\ pc[t] = "idle"
  /\ pc' = [pc EXCEPT ![t] = "try_attempt"]
  /\ UNCHANGED <<lock, owner, waitQueue>>

AttemptLock(t) == 
  /\ pc[t] = "lock_attempt"
  /\ IF lock = FALSE
        THEN /\ lock' = TRUE
             /\ owner' = t
             /\ pc' = [pc EXCEPT ![t] = "in_cs"]
             /\ waitQueue' = waitQueue
        ELSE /\ waitQueue' = Append(waitQueue, t)
             /\ pc' = [pc EXCEPT ![t] = "waiting"]
             /\ UNCHANGED <<lock, owner>>
  /\ UNCHANGED <<>>

TryLock(t) == 
  /\ pc[t] = "try_attempt"
  /\ IF lock = FALSE
        THEN /\ lock' = TRUE
             /\ owner' = t
             /\ pc' = [pc EXCEPT ![t] = "in_cs"]
        ELSE /\ pc' = [pc EXCEPT ![t] = "idle"]
  /\ UNCHANGED <<owner, waitQueue>>

Unlock(t) == 
  /\ pc[t] = "in_cs"
  /\ owner = t
  /\ lock' = FALSE
  /\ owner' = NoThread
  /\ IF waitQueue = <<>>
        THEN /\ waitQueue' = waitQueue
             /\ pc' = [pc EXCEPT ![t] = "idle"]
        ELSE /\ LET t0 == Head(waitQueue)
             IN /\ waitQueue' = Tail(waitQueue)
                /\ pc' = [pc EXCEPT ![t] = "idle", ![t0] = "lock_attempt"]

Next == 
  \/ \E t \in Threads : StartLock(t)
  \/ \E t \in Threads : StartTryLock(t)
  \/ \E t \in Threads : AttemptLock(t)
  \/ \E t \in Threads : TryLock(t)
  \/ \E t \in Threads : Unlock(t)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====