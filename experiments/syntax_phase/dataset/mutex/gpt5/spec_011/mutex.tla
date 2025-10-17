---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS THREADS, None

VARIABLES lock, owner, queue, mode, guard

Modes == {"Free", "Blocked", "Ready", "Holding"}

Head(s) == s[1]
Tail(s) == SubSeq(s, 2, Len(s))
InSeq(x, s) == ∃ i ∈ 1..Len(s): s[i] = x

TypeOK ==
  /\ lock \in BOOLEAN
  /\ owner \in THREADS \cup {None}
  /\ queue \in Seq(THREADS)
  /\ mode \in [THREADS -> Modes]
  /\ guard \in [THREADS -> BOOLEAN]
  /\ (lock = FALSE =>
        /\ owner = None
        /\ \A t \in THREADS: guard[t] = FALSE)
  /\ (lock = TRUE =>
        /\ owner \in THREADS
        /\ guard[owner] = TRUE
        /\ \A t \in THREADS \ {owner}: guard[t] = FALSE)

Init ==
  /\ lock = FALSE
  /\ owner = None
  /\ queue = << >>
  /\ mode = [t \in THREADS |-> "Free"]
  /\ guard = [t \in THREADS |-> FALSE]
  /\ TypeOK

TryLockAcquire(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Free"
  /\ lock = FALSE
  /\ owner = None
  /\ lock' = TRUE
  /\ owner' = t
  /\ guard' = [guard EXCEPT ![t] = TRUE]
  /\ mode' = [mode EXCEPT ![t] = "Holding"]
  /\ queue' = queue

LockAcquireDirect(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Free"
  /\ lock = FALSE
  /\ owner = None
  /\ lock' = TRUE
  /\ owner' = t
  /\ guard' = [guard EXCEPT ![t] = TRUE]
  /\ mode' = [mode EXCEPT ![t] = "Holding"]
  /\ queue' = queue

LockEnqueue(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Free"
  /\ lock = TRUE
  /\ ~InSeq(t, queue)
  /\ queue' = Append(queue, t)
  /\ mode' = [mode EXCEPT ![t] = "Blocked"]
  /\ UNCHANGED <<lock, owner, guard>>

ReadyAcquire(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Ready"
  /\ lock = FALSE
  /\ owner = None
  /\ lock' = TRUE
  /\ owner' = t
  /\ guard' = [guard EXCEPT ![t] = TRUE]
  /\ mode' = [mode EXCEPT ![t] = "Holding"]
  /\ queue' = queue

ReadyFailRequeue(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Ready"
  /\ lock = TRUE
  /\ ~InSeq(t, queue)
  /\ queue' = Append(queue, t)
  /\ mode' = [mode EXCEPT ![t] = "Blocked"]
  /\ UNCHANGED <<lock, owner, guard>>

UnlockAndWake(t) ==
  /\ t \in THREADS
  /\ mode[t] = "Holding"
  /\ owner = t
  /\ lock = TRUE
  /\ guard[t] = TRUE
  /\ lock' = FALSE
  /\ owner' = None
  /\ guard' = [guard EXCEPT ![t] = FALSE]
  /\ IF Len(queue) = 0 THEN
       /\ queue' = queue
       /\ mode' = [mode EXCEPT ![t] = "Free"]
     ELSE
       LET u == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ mode' = [mode EXCEPT ![t] = "Free", ![u] = "Ready"]

Next ==
  \E t \in THREADS:
      TryLockAcquire(t)
    \/ LockAcquireDirect(t)
    \/ LockEnqueue(t)
    \/ ReadyAcquire(t)
    \/ ReadyFailRequeue(t)
    \/ UnlockAndWake(t)

Vars == <<lock, owner, queue, mode, guard>>

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A t \in THREADS: WF_Vars(ReadyAcquire(t))

====