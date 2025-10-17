---- MODULE spin ----

EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    Threads,
    MaxSpins

VARIABLES
    lockState,
    threadStates,
    guardStates,
    spinning,
    acquisitionOrder,
    pc

vars == <<lockState, threadStates, guardStates, spinning, acquisitionOrder, pc>>

ThreadState == {"idle", "acquiring", "spinning", "holding", "releasing"}
GuardType == {"PreemptDisabled", "LocalIrqDisabled"}
LockState == {"unlocked", "locked"}

TypeInvariant ==
    /\ lockState \in LockState
    /\ threadStates \in [Threads -> ThreadState]
    /\ guardStates \in [Threads -> GuardType \cup {"none"}]
    /\ spinning \in [Threads -> Nat]
    /\ acquisitionOrder \in Seq(Threads)
    /\ pc \in [Threads -> {"init", "guard_created", "try_acquire", "spin_wait", "acquired", "critical", "release", "done"}]

Init ==
    /\ lockState = "unlocked"
    /\ threadStates = [t \in Threads |-> "idle"]
    /\ guardStates = [t \in Threads |-> "none"]
    /\ spinning = [t \in Threads |-> 0]
    /\ acquisitionOrder = <<>>
    /\ pc = [t \in Threads |-> "init"]

CreateGuard(t) ==
    /\ pc[t] = "init"
    /\ threadStates[t] = "idle"
    /\ guardStates' = [guardStates EXCEPT ![t] = "PreemptDisabled"]
    /\ threadStates' = [threadStates EXCEPT ![t] = "acquiring"]
    /\ pc' = [pc EXCEPT ![t] = "guard_created"]
    /\ UNCHANGED <<lockState, spinning, acquisitionOrder>>

DisableIrq(t) ==
    /\ guardStates[t] = "PreemptDisabled"
    /\ guardStates' = [guardStates EXCEPT ![t] = "LocalIrqDisabled"]
    /\ UNCHANGED <<lockState, threadStates, spinning, acquisitionOrder, pc>>

TryAcquireLock(t) ==
    /\ pc[t] = "guard_created"
    /\ threadStates[t] = "acquiring"
    /\ IF lockState = "unlocked"
       THEN /\ lockState' = "locked"
            /\ threadStates' = [threadStates EXCEPT ![t] = "holding"]
            /\ acquisitionOrder' = Append(acquisitionOrder, t)
            /\ pc' = [pc EXCEPT ![t] = "acquired"]
            /\ UNCHANGED spinning
       ELSE /\ threadStates' = [threadStates EXCEPT ![t] = "spinning"]
            /\ pc' = [pc EXCEPT ![t] = "spin_wait"]
            /\ UNCHANGED <<lockState, spinning, acquisitionOrder>>
    /\ UNCHANGED guardStates

SpinWait(t) ==
    /\ pc[t] = "spin_wait"
    /\ threadStates[t] = "spinning"
    /\ spinning[t] < MaxSpins
    /\ spinning' = [spinning EXCEPT ![t] = @ + 1]
    /\ pc' = [pc EXCEPT ![t] = "try_acquire"]
    /\ UNCHANGED <<lockState, threadStates, guardStates, acquisitionOrder>>

RetryAcquire(t) ==
    /\ pc[t] = "try_acquire"
    /\ threadStates[t] = "spinning"
    /\ IF lockState = "unlocked"
       THEN /\ lockState' = "locked"
            /\ threadStates' = [threadStates EXCEPT ![t] = "holding"]
            /\ acquisitionOrder' = Append(acquisitionOrder, t)
            /\ pc' = [pc EXCEPT ![t] = "acquired"]
            /\ UNCHANGED spinning
       ELSE /\ pc' = [pc EXCEPT ![t] = "spin_wait"]
            /\ UNCHANGED <<lockState, threadStates, spinning, acquisitionOrder>>
    /\ UNCHANGED guardStates

EnterCriticalSection(t) ==
    /\ pc[t] = "acquired"
    /\ threadStates[t] = "holding"
    /\ pc' = [pc EXCEPT ![t] = "critical"]
    /\ UNCHANGED <<lockState, threadStates, guardStates, spinning, acquisitionOrder>>

ExitCriticalSection(t) ==
    /\ pc[t] = "critical"
    /\ threadStates[t] = "holding"
    /\ pc' = [pc EXCEPT ![t] = "release"]
    /\ UNCHANGED <<lockState, threadStates, guardStates, spinning, acquisitionOrder>>

ReleaseLock(t) ==
    /\ pc[t] = "release"
    /\ threadStates[t] = "holding"
    /\ lockState = "locked"
    /\ lockState' = "unlocked"
    /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
    /\ guardStates' = [guardStates EXCEPT ![t] = "none"]
    /\ acquisitionOrder' = SelectSeq(acquisitionOrder, LAMBDA x: x # t)
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED spinning

TryLockSuccess(t) ==
    /\ pc[t] = "guard_created"
    /\ threadStates[t] = "acquiring"
    /\ lockState = "unlocked"
    /\ lockState' = "locked"
    /\ threadStates' = [threadStates EXCEPT ![t] = "holding"]
    /\ acquisitionOrder' = Append(acquisitionOrder, t)
    /\ pc' = [pc EXCEPT ![t] = "acquired"]
    /\ UNCHANGED <<guardStates, spinning>>

TryLockFail(t) ==
    /\ pc[t] = "guard_created"
    /\ threadStates[t] = "acquiring"
    /\ lockState = "locked"
    /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
    /\ guardStates' = [guardStates EXCEPT ![t] = "none"]
    /\ pc' = [pc EXCEPT ![t] = "done"]
    /\ UNCHANGED <<lockState, spinning, acquisitionOrder>>

Next ==
    \E t \in Threads:
        \/ CreateGuard(t)
        \/ DisableIrq(t)
        \/ TryAcquireLock(t)
        \/ SpinWait(t)
        \/ RetryAcquire(t)
        \/ EnterCriticalSection(t)
        \/ ExitCriticalSection(t)
        \/ ReleaseLock(t)
        \/ TryLockSuccess(t)
        \/ TryLockFail(t)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    Cardinality({t \in Threads : threadStates[t] = "holding"}) <= 1

NoDeadlock ==
    (lockState = "locked") => (\E t \in Threads : threadStates[t] = "holding")

LockProgress ==
    \A t \in Threads : 
        (threadStates[t] = "spinning") ~> (threadStates[t] # "spinning")

GuardConsistency ==
    \A t \in Threads :
        (threadStates[t] = "holding") => (guardStates[t] \in GuardType)

AtomicAcquisition ==
    \A t \in Threads :
        (pc[t] = "try_acquire" /\ lockState = "unlocked") =>
        (lockState' = "locked" /\ threadStates'[t] = "holding")

SpinBound ==
    \A t \in Threads : spinning[t] <= MaxSpins

AcquisitionOrdering ==
    \A i, j \in 1..Len(acquisitionOrder) :
        i < j => acquisitionOrder[i] # acquisitionOrder[j]

====