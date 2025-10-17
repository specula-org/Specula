---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, Nil

VARIABLES lock, owner, queue, thrState, guard, gate

vars == << lock, owner, queue, thrState, guard, gate >>

InSeq(s, x) == \E i \in 1..Len(s): s[i] = x

CanAcquireFree(t) ==
  /\ lock = FALSE
  /\ owner = Nil
  /\ gate = Nil
  /\ queue = << >>
  /\ guard[t] = FALSE
  /\ thrState[t] = "Running"

CanAcquireHead(t) ==
  /\ lock = FALSE
  /\ owner = Nil
  /\ gate = Nil
  /\ queue # << >>
  /\ Head(queue) = t
  /\ guard[t] = FALSE
  /\ thrState[t] = "Running"

CanAcquireGate(t) ==
  /\ lock = FALSE
  /\ owner = Nil
  /\ gate = t
  /\ guard[t] = FALSE
  /\ thrState[t] = "Running"

TypeOK ==
  /\ lock \in BOOLEAN
  /\ owner \in Threads \cup {Nil}
  /\ IsSeq(queue) /\ \A i \in DOMAIN queue: queue[i] \in Threads
  /\ thrState \in [Threads -> {"Running", "Waiting"}]
  /\ guard \in [Threads -> BOOLEAN]
  /\ gate \in Threads \cup {Nil}

Init ==
  /\ TypeOK
  /\ lock = FALSE
  /\ owner = Nil
  /\ queue = << >>
  /\ thrState = [t \in Threads |-> "Running"]
  /\ guard = [t \in Threads |-> FALSE]
  /\ gate = Nil

\* Fixed syntax: group disjunction branches in parentheses to avoid '/\ \/'' parse issue.
TryLock(t) ==
  /\ t \in Threads
  /\ thrState[t] = "Running"
  /\ guard[t] = FALSE
  /\ (
       \/ /\ CanAcquireFree(t)
          /\ lock' = TRUE
          /\ owner' = t
          /\ guard' = [guard EXCEPT ![t] = TRUE]
          /\ UNCHANGED << queue, thrState, gate >>
       \/ /\ CanAcquireHead(t)
          /\ lock' = TRUE
          /\ owner' = t
          /\ guard' = [guard EXCEPT ![t] = TRUE]
          /\ queue' = Tail(queue)
          /\ UNCHANGED << thrState, gate >>
       \/ /\ CanAcquireGate(t)
          /\ lock' = TRUE
          /\ owner' = t
          /\ guard' = [guard EXCEPT ![t] = TRUE]
          /\ gate' = Nil
          /\ UNCHANGED << queue, thrState >>
       \/ /\ ~ (CanAcquireFree(t) \/ CanAcquireHead(t) \/ CanAcquireGate(t))
          /\ UNCHANGED vars
     )

\* Fixed syntax: group disjunction branches in parentheses to avoid '/\ \/'' parse issue.
LockCall(t) ==
  /\ t \in Threads
  /\ thrState[t] = "Running"
  /\ guard[t] = FALSE
  /\ (
       \/ /\ CanAcquireFree(t)
          /\ lock' = TRUE
          /\ owner' = t
          /\ guard' = [guard EXCEPT ![t] = TRUE]
          /\ UNCHANGED << queue, thrState, gate >>
       \/ /\ CanAcquireHead(t)
          /\ lock' = TRUE
          /\ owner' = t
          /\ guard' = [guard EXCEPT ![t] = TRUE]
          /\ queue' = Tail(queue)
          /\ UNCHANGED << thrState, gate >>
       \/ /\ CanAcquireGate(t)
          /\ lock' = TRUE
          /\ owner' = t
          /\ guard' = [guard EXCEPT ![t] = TRUE]
          /\ gate' = Nil
          /\ UNCHANGED << queue, thrState >>
       \/ /\ ~ (CanAcquireFree(t) \/ CanAcquireHead(t) \/ CanAcquireGate(t))
          /\ UNCHANGED vars
     )

EnqueueAndBlock(t) ==
  /\ t \in Threads
  /\ thrState[t] = "Running"
  /\ guard[t] = FALSE
  /\ lock = TRUE
  /\ ~InSeq(queue, t)
  /\ queue' = queue \o << t >>
  /\ thrState' = [thrState EXCEPT ![t] = "Waiting"]
  /\ UNCHANGED << lock, owner, guard, gate >>

WakeOne ==
  \E u \in Threads:
    /\ queue # << >>
    /\ u = Head(queue)
    /\ queue' = Tail(queue)
    /\ thrState' = [thrState EXCEPT ![u] = "Running"]
    /\ gate' = u

Unlock(t) ==
  /\ t \in Threads
  /\ owner = t
  /\ guard[t] = TRUE
  /\ lock = TRUE
  /\ lock' = FALSE
  /\ owner' = Nil
  /\ guard' = [guard EXCEPT ![t] = FALSE]
  /\ IF queue = << >> THEN
       /\ queue' = queue
       /\ gate' = Nil
       /\ UNCHANGED thrState
     ELSE
       /\ WakeOne

AcquireHead(t) ==
  /\ t \in Threads
  /\ CanAcquireHead(t)
  /\ lock' = TRUE
  /\ owner' = t
  /\ guard' = [guard EXCEPT ![t] = TRUE]
  /\ queue' = Tail(queue)
  /\ UNCHANGED << thrState, gate >>

AcquireGate(t) ==
  /\ t \in Threads
  /\ CanAcquireGate(t)
  /\ lock' = TRUE
  /\ owner' = t
  /\ guard' = [guard EXCEPT ![t] = TRUE]
  /\ gate' = Nil
  /\ UNCHANGED << queue, thrState >>

Next ==
  \E t \in Threads:
    \/ TryLock(t)
    \/ LockCall(t)
    \/ EnqueueAndBlock(t)
    \/ Unlock(t)
    \/ AcquireHead(t)
    \/ AcquireGate(t)

Spec ==
  Init /\ [][Next]_vars
  /\ (\A t \in Threads: WF_vars(Unlock(t)))
  /\ (\A t \in Threads: SF_vars(AcquireGate(t)))
  /\ (\A t \in Threads: SF_vars(AcquireHead(t)))

====