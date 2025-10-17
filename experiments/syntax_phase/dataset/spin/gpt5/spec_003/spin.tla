---- MODULE spin ----
EXTENDS Naturals, Sequences

CONSTANTS THREADS, None

ASSUME None \notin THREADS

VARIABLES lock, owner, pc, guard, spins, epoch, view

TypeOK ==
  /\ lock \in BOOLEAN
  /\ owner \in THREADS \cup {None}
  /\ pc \in [THREADS -> {"Ready", "Trying", "InCS"}]
  /\ guard \in [THREADS -> BOOLEAN]
  /\ spins \in [THREADS -> Nat]
  /\ epoch \in Nat
  /\ view \in [THREADS -> Nat]

Init ==
  /\ lock = FALSE
  /\ owner = None
  /\ pc = [t \in THREADS |-> "Ready"]
  /\ guard = [t \in THREADS |-> FALSE]
  /\ spins = [t \in THREADS |-> 0]
  /\ epoch = 0
  /\ view = [t \in THREADS |-> 0]

LockBegin(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Ready"
  /\ guard' = [guard EXCEPT ![t] = TRUE]
  /\ pc' = [pc EXCEPT ![t] = "Trying"]
  /\ UNCHANGED <<lock, owner, spins, epoch, view>>

TryLockSuccess(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Ready"
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ owner' = t
  /\ pc' = [pc EXCEPT ![t] = "InCS"]
  /\ guard' = [guard EXCEPT ![t] = TRUE]
  /\ view' = [view EXCEPT ![t] = epoch]
  /\ UNCHANGED <<spins, epoch>>

TryLockFail(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Ready"
  /\ lock = TRUE
  /\ guard' = [guard EXCEPT ![t] = FALSE]
  /\ UNCHANGED <<lock, owner, pc, spins, epoch, view>>

Spin(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Trying"
  /\ lock = TRUE
  /\ spins' = [spins EXCEPT ![t] = @ + 1]
  /\ UNCHANGED <<lock, owner, pc, guard, epoch, view>>

AcquireCAS(t) ==
  /\ t \in THREADS
  /\ pc[t] = "Trying"
  /\ guard[t] = TRUE
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ owner' = t
  /\ pc' = [pc EXCEPT ![t] = "InCS"]
  /\ view' = [view EXCEPT ![t] = epoch]
  /\ UNCHANGED <<guard, spins, epoch>>

Unlock(t) ==
  /\ t \in THREADS
  /\ pc[t] = "InCS"
  /\ owner = t
  /\ lock' = FALSE
  /\ owner' = None
  /\ pc' = [pc EXCEPT ![t] = "Ready"]
  /\ guard' = [guard EXCEPT ![t] = FALSE]
  /\ epoch' = epoch + 1
  /\ UNCHANGED <<spins, view>>

Next ==
  \E t \in THREADS:
      LockBegin(t)
    \/ TryLockSuccess(t)
    \/ TryLockFail(t)
    \/ Spin(t)
    \/ AcquireCAS(t)
    \/ Unlock(t)

Vars == <<lock, owner, pc, guard, spins, epoch, view>>

Spec ==
  Init /\ [][Next]_Vars /\ Fairness

Fairness ==
  /\ \A t \in THREADS: WF_Vars(AcquireCAS(t))
  /\ \A t \in THREADS: WF_Vars(Unlock(t))

OwnerLockConsistency ==
  /\ (owner \in THREADS) <=> lock
  /\ (owner = None) <=> ~lock

MutualExclusion ==
  \A t1, t2 \in THREADS:
    t1 # t2 => ~(pc[t1] = "InCS" /\ pc[t2] = "InCS")

RAII ==
  \A t \in THREADS:
    pc[t] = "InCS" => guard[t] = TRUE

AcquireReleaseOrder ==
  \A t \in THREADS: view[t] \leq epoch

Invariant ==
  TypeOK /\ OwnerLockConsistency /\ MutualExclusion /\ RAII /\ AcquireReleaseOrder
====