---- MODULE spin ----

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS 
    Threads,
    MaxSpins

VARIABLES
    lockState,
    guardState,
    spinning,
    waitQueue,
    pc

vars == <<lockState, guardState, spinning, waitQueue, pc>>

ThreadStates == {"idle", "acquiring", "spinning", "locked", "releasing"}
LockStates == {"unlocked", "locked"}
GuardTypes == {"PreemptDisabled", "LocalIrqDisabled"}

TypeInvariant ==
    /\ lockState \in LockStates
    /\ guardState \in [Threads -> GuardTypes \cup {"none"}]
    /\ spinning \in [Threads -> Nat]
    /\ waitQueue \in Seq(Threads)
    /\ pc \in [Threads -> ThreadStates]

Init ==
    /\ lockState = "unlocked"
    /\ guardState = [t \in Threads |-> "none"]
    /\ spinning = [t \in Threads |-> 0]
    /\ waitQueue = <<>>
    /\ pc = [t \in Threads |-> "idle"]

TryAcquireLock(t) ==
    /\ pc[t] = "acquiring"
    /\ IF lockState = "unlocked"
       THEN /\ lockState' = "locked"
            /\ pc' = [pc EXCEPT ![t] = "locked"]
            /\ UNCHANGED <<guardState, spinning, waitQueue>>
       ELSE /\ pc' = [pc EXCEPT ![t] = "spinning"]
            /\ waitQueue' = Append(waitQueue, t)
            /\ UNCHANGED <<lockState, guardState, spinning>>

SpinWait(t) ==
    /\ pc[t] = "spinning"
    /\ lockState = "locked"
    /\ spinning[t] < MaxSpins
    /\ spinning' = [spinning EXCEPT ![t] = @ + 1]
    /\ pc' = [pc EXCEPT ![t] = "acquiring"]
    /\ UNCHANGED <<lockState, guardState, waitQueue>>

AcquireLock(t) ==
    /\ pc[t] = "idle"
    /\ guardState' = [guardState EXCEPT ![t] = "PreemptDisabled"]
    /\ pc' = [pc EXCEPT ![t] = "acquiring"]
    /\ UNCHANGED <<lockState, spinning, waitQueue>>

AcquireLockWithIrqDisabled(t) ==
    /\ pc[t] = "idle"
    /\ guardState' = [guardState EXCEPT ![t] = "LocalIrqDisabled"]
    /\ pc' = [pc EXCEPT ![t] = "acquiring"]
    /\ UNCHANGED <<lockState, spinning, waitQueue>>

ReleaseLock(t) ==
    /\ pc[t] = "locked"
    /\ lockState = "locked"
    /\ lockState' = "unlocked"
    /\ guardState' = [guardState EXCEPT ![t] = "none"]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ spinning' = [spinning EXCEPT ![t] = 0]
    /\ waitQueue' = IF Len(waitQueue) > 0 /\ Head(waitQueue) = t
                    THEN Tail(waitQueue)
                    ELSE waitQueue

TryLock(t) ==
    /\ pc[t] = "idle"
    /\ guardState' = [guardState EXCEPT ![t] = "PreemptDisabled"]
    /\ IF lockState = "unlocked"
       THEN /\ lockState' = "locked"
            /\ pc' = [pc EXCEPT ![t] = "locked"]
            /\ UNCHANGED <<spinning, waitQueue>>
       ELSE /\ pc' = [pc EXCEPT ![t] = "idle"]
            /\ guardState' = [guardState EXCEPT ![t] = "none"]
            /\ UNCHANGED <<lockState, spinning, waitQueue>>

CompareAndSwap(t) ==
    /\ pc[t] = "acquiring"
    /\ IF lockState = "unlocked"
       THEN /\ lockState' = "locked"
            /\ pc' = [pc EXCEPT ![t] = "locked"]
            /\ UNCHANGED <<guardState, spinning, waitQueue>>
       ELSE /\ UNCHANGED <<lockState, guardState, spinning, waitQueue, pc>>

AtomicStore(t) ==
    /\ pc[t] = "locked"
    /\ lockState = "locked"
    /\ lockState' = "unlocked"
    /\ UNCHANGED <<guardState, spinning, waitQueue, pc>>

Next ==
    \E t \in Threads:
        \/ AcquireLock(t)
        \/ AcquireLockWithIrqDisabled(t)
        \/ TryAcquireLock(t)
        \/ SpinWait(t)
        \/ ReleaseLock(t)
        \/ TryLock(t)
        \/ CompareAndSwap(t)
        \/ AtomicStore(t)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    Cardinality({t \in Threads : pc[t] = "locked"}) <= 1

LockFreedom ==
    (lockState = "unlocked") => 
        (\E t \in Threads : pc[t] = "acquiring" => <>(pc[t] = "locked"))

NoDeadlock ==
    (\E t \in Threads : pc[t] = "acquiring") => 
        <>(\E t \in Threads : pc[t] = "locked")

GuardConsistency ==
    \A t \in Threads : 
        (pc[t] = "locked") => (guardState[t] \in GuardTypes)

AtomicityProperty ==
    \A t \in Threads :
        (pc[t] = "acquiring" /\ lockState = "unlocked") =>
            (lockState' = "locked" => pc'[t] = "locked")

SpinBound ==
    \A t \in Threads : spinning[t] <= MaxSpins

EventualProgress ==
    \A t \in Threads :
        (pc[t] = "acquiring") ~> (pc[t] = "locked" \/ pc[t] = "idle")

MemoryOrdering ==
    \A t \in Threads :
        /\ (pc[t] = "acquiring" /\ pc'[t] = "locked") => 
           (lockState = "unlocked" /\ lockState' = "locked")
        /\ (pc[t] = "locked" /\ pc'[t] = "idle") =>
           (lockState = "locked" /\ lockState' = "unlocked")

GuardUpgrade ==
    \A t \in Threads :
        (guardState[t] = "PreemptDisabled") =>
            (guardState'[t] \in {"PreemptDisabled", "LocalIrqDisabled", "none"})

FairAcquisition ==
    \A t \in Threads :
        WF_vars(TryAcquireLock(t)) /\ WF_vars(ReleaseLock(t))

THEOREM Spec => []MutualExclusion
THEOREM Spec => []LockFreedom  
THEOREM Spec => []NoDeadlock
THEOREM Spec => []GuardConsistency
THEOREM Spec => []AtomicityProperty
THEOREM Spec => []SpinBound
THEOREM Spec => []EventualProgress
THEOREM Spec => []MemoryOrdering
THEOREM Spec => []GuardUpgrade

====