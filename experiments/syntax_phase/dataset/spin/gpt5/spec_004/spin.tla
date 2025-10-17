---- MODULE spin ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS T

VARIABLES lock, owner, phase, guard, spins, E, epoch, view

TypeOK ==
    /\ lock \in BOOLEAN
    /\ owner \in (T \cup {"None"})
    /\ phase \in [T -> {"Idle","Trying","Spinning","InCS"}]
    /\ guard \in [T -> {"None","Prepared","Held"}]
    /\ spins \in [T -> Nat]
    /\ E \in Seq([type : {"Acquire","Release"}, t : T])
    /\ epoch \in Nat
    /\ view \in [T -> Nat]

Init ==
    /\ lock = FALSE
    /\ owner = "None"
    /\ phase = [t \in T |-> "Idle"]
    /\ guard = [t \in T |-> "None"]
    /\ spins = [t \in T |-> 0]
    /\ E = << >>
    /\ epoch = 0
    /\ view = [t \in T |-> 0]

LockCall(t) ==
    /\ t \in T
    /\ phase[t] = "Idle"
    /\ phase' = [phase EXCEPT ![t] = "Trying"]
    /\ guard' = [guard EXCEPT ![t] = "Prepared"]
    /\ UNCHANGED << lock, owner, spins, E, epoch, view >>

TryAcquireCAS(t) ==
    /\ t \in T
    /\ phase[t] \in {"Trying","Spinning"}
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ owner' = t
    /\ phase' = [phase EXCEPT ![t] = "InCS"]
    /\ guard' = [guard EXCEPT ![t] = "Held"]
    /\ E' = Append(E, [type |-> "Acquire", t |-> t])
    /\ view' = [view EXCEPT ![t] = epoch]
    /\ UNCHANGED << spins, epoch >>

SpinStep(t) ==
    /\ t \in T
    /\ phase[t] \in {"Trying","Spinning"}
    /\ lock = TRUE
    /\ phase' = [phase EXCEPT ![t] = "Spinning"]
    /\ spins' = [spins EXCEPT ![t] = spins[t] + 1]
    /\ UNCHANGED << lock, owner, guard, E, epoch, view >>

TryLockSuccess(t) ==
    /\ t \in T
    /\ phase[t] = "Idle"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ owner' = t
    /\ phase' = [phase EXCEPT ![t] = "InCS"]
    /\ guard' = [guard EXCEPT ![t] = "Held"]
    /\ E' = Append(E, [type |-> "Acquire", t |-> t])
    /\ view' = [view EXCEPT ![t] = epoch]
    /\ UNCHANGED << spins, epoch >>

TryLockFail(t) ==
    /\ t \in T
    /\ phase[t] = "Idle"
    /\ lock = TRUE
    /\ phase' = phase
    /\ guard' = [guard EXCEPT ![t] = "None"]
    /\ UNCHANGED << lock, owner, spins, E, epoch, view >>

Unlock(t) ==
    /\ t \in T
    /\ phase[t] = "InCS"
    /\ owner = t
    /\ lock' = FALSE
    /\ owner' = "None"
    /\ phase' = [phase EXCEPT ![t] = "Idle"]
    /\ guard' = [guard EXCEPT ![t] = "None"]
    /\ epoch' = epoch + 1
    /\ E' = Append(E, [type |-> "Release", t |-> t])
    /\ UNCHANGED << spins, view >>

Next ==
    \E t \in T:
        LockCall(t)
        \/ TryAcquireCAS(t)
        \/ SpinStep(t)
        \/ TryLockSuccess(t)
        \/ TryLockFail(t)
        \/ Unlock(t)

Vars == << lock, owner, phase, guard, spins, E, epoch, view >>

Spec ==
    Init /\ [][Next]_Vars /\ \A t \in T : SF_vars(TryAcquireCAS(t))
====