---- MODULE spin ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, Values, None

VARIABLES lock, owner, pc, guard, data, local, version, spins, acqver

PCStates == {"Idle", "Trying", "Spinning", "Try", "Holding"}

TypeOK ==
  /\ lock \in BOOLEAN
  /\ owner \in (Threads \cup {None})
  /\ pc \in [Threads -> PCStates]
  /\ guard \in [Threads -> BOOLEAN]
  /\ data \in Values
  /\ local \in [Threads -> Values]
  /\ version \in Nat
  /\ spins \in [Threads -> Nat]
  /\ acqver \in [Threads -> Nat]

Init ==
  /\ lock = FALSE
  /\ owner = None
  /\ \E v \in Values :
       /\ data = v
       /\ local = [i \in Threads |-> v]
  /\ version = 0
  /\ acqver = [i \in Threads |-> 0]
  /\ spins = [i \in Threads |-> 0]
  /\ pc = [i \in Threads |-> "Idle"]
  /\ guard = [i \in Threads |-> FALSE]

LockBegin(i) ==
  /\ i \in Threads
  /\ pc[i] = "Idle"
  /\ pc' = [pc EXCEPT ![i] = "Trying"]
  /\ guard' = [guard EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<lock, owner, data, local, version, spins, acqver>>

LockCAS(i) ==
  /\ i \in Threads
  /\ pc[i] \in {"Trying", "Spinning"}
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ owner' = i
  /\ pc' = [pc EXCEPT ![i] = "Holding"]
  /\ guard' = guard
  /\ acqver' = [acqver EXCEPT ![i] = version]
  /\ local' = [local EXCEPT ![i] = data]
  /\ UNCHANGED <<data, spins, version>>

SpinLoop(i) ==
  /\ i \in Threads
  /\ pc[i] \in {"Trying", "Spinning"}
  /\ lock = TRUE
  /\ spins' = [spins EXCEPT ![i] = @ + 1]
  /\ pc' = [pc EXCEPT ![i] = "Spinning"]
  /\ UNCHANGED <<lock, owner, data, local, version, acqver, guard>>

TryLockBegin(i) ==
  /\ i \in Threads
  /\ pc[i] = "Idle"
  /\ pc' = [pc EXCEPT ![i] = "Try"]
  /\ guard' = [guard EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<lock, owner, data, local, version, spins, acqver>>

TryLockSuccess(i) ==
  /\ i \in Threads
  /\ pc[i] = "Try"
  /\ lock = FALSE
  /\ lock' = TRUE
  /\ owner' = i
  /\ pc' = [pc EXCEPT ![i] = "Holding"]
  /\ guard' = guard
  /\ acqver' = [acqver EXCEPT ![i] = version]
  /\ local' = [local EXCEPT ![i] = data]
  /\ UNCHANGED <<data, spins, version>>

TryLockFail(i) ==
  /\ i \in Threads
  /\ pc[i] = "Try"
  /\ lock = TRUE
  /\ pc' = [pc EXCEPT ![i] = "Idle"]
  /\ guard' = [guard EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<lock, owner, data, local, version, spins, acqver>>

Unlock(i) ==
  /\ i \in Threads
  /\ pc[i] = "Holding"
  /\ owner = i
  /\ lock = TRUE
  /\ version' = version + 1
  /\ data' = local[i]
  /\ lock' = FALSE
  /\ owner' = None
  /\ pc' = [pc EXCEPT ![i] = "Idle"]
  /\ guard' = [guard EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<local, spins, acqver>>

WriteCS(i) ==
  /\ i \in Threads
  /\ pc[i] = "Holding"
  /\ \E v \in Values : local' = [local EXCEPT ![i] = v]
  /\ UNCHANGED <<lock, owner, data, version, spins, acqver, guard, pc>>

lock(i) ==
  LockBegin(i) \/ LockCAS(i) \/ SpinLoop(i)

try_lock(i) ==
  TryLockBegin(i) \/ TryLockSuccess(i) \/ TryLockFail(i)

unlock(i) ==
  Unlock(i)

write_cs(i) ==
  WriteCS(i)

Next ==
  \E i \in Threads :
    lock(i) \/ try_lock(i) \/ unlock(i) \/ write_cs(i)

Vars == <<lock, owner, pc, guard, data, local, version, spins, acqver>>

Spec ==
  Init /\ [][Next]_Vars /\ WF_Vars(Next)
====
