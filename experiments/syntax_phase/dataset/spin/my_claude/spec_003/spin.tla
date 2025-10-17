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
ProgramCounter == {"Init", "TryLock", "Spin", "Acquired", "Critical", "Release", "Done"}

TypeInvariant ==
    /\ lockState \in BOOLEAN
    /\ threadStates \in [Threads -> ThreadState]
    /\ guardStates \in [Threads -> GuardType \cup {"none"}]
    /\ spinning \in [Threads -> Nat]
    /\ acquisitionOrder \in Seq(Threads)
    /\ pc \in [Threads -> ProgramCounter]

Init ==
    /\ lockState = FALSE
    /\ threadStates = [t \in Threads |-> "idle"]
    /\ guardStates = [t \in Threads |-> "none"]
    /\ spinning = [t \in Threads |-> 0]
    /\ acquisitionOrder = <<>>
    /\ pc = [t \in Threads |-> "Init"]

CompareAndSwap(expected, new) ==
    IF lockState = expected
    THEN /\ lockState' = new
         /\ TRUE
    ELSE /\ UNCHANGED lockState
         /\ FALSE

AtomicLoad ==
    lockState

AtomicStore(value) ==
    lockState' = value

StartLock(t) ==
    /\ pc[t] = "Init"
    /\ threadStates[t] = "idle"
    /\ threadStates' = [threadStates EXCEPT ![t] = "acquiring"]
    /\ guardStates' = [guardStates EXCEPT ![t] = "PreemptDisabled"]
    /\ pc' = [pc EXCEPT ![t] = "TryLock"]
    /\ UNCHANGED <<lockState, spinning, acquisitionOrder>>

TryAcquireLock(t) ==
    /\ pc[t] = "TryLock"
    /\ threadStates[t] = "acquiring"
    /\ LET success == CompareAndSwap(FALSE, TRUE)
       IN IF success
          THEN /\ threadStates' = [threadStates EXCEPT ![t] = "holding"]
               /\ pc' = [pc EXCEPT ![t] = "Acquired"]
               /\ acquisitionOrder' = Append(acquisitionOrder, t)
               /\ UNCHANGED <<spinning, guardStates>>
          ELSE /\ threadStates' = [threadStates EXCEPT ![t] = "spinning"]
               /\ pc' = [pc EXCEPT ![t] = "Spin"]
               /\ spinning' = [spinning EXCEPT ![t] = spinning[t] + 1]
               /\ UNCHANGED <<acquisitionOrder, guardStates>>

SpinWait(t) ==
    /\ pc[t] = "Spin"
    /\ threadStates[t] = "spinning"
    /\ spinning[t] < MaxSpins
    /\ LET success == CompareAndSwap(FALSE, TRUE)
       IN IF success
          THEN /\ threadStates' = [threadStates EXCEPT ![t] = "holding"]
               /\ pc' = [pc EXCEPT ![t] = "Acquired"]
               /\ acquisitionOrder' = Append(acquisitionOrder, t)
               /\ UNCHANGED <<spinning, guardStates>>
          ELSE /\ spinning' = [spinning EXCEPT ![t] = spinning[t] + 1]
               /\ UNCHANGED <<threadStates, pc, acquisitionOrder, guardStates>>

AcquiredLock(t) ==
    /\ pc[t] = "Acquired"
    /\ threadStates[t] = "holding"
    /\ pc' = [pc EXCEPT ![t] = "Critical"]
    /\ UNCHANGED <<lockState, threadStates, guardStates, spinning, acquisitionOrder>>

CriticalSection(t) ==
    /\ pc[t] = "Critical"
    /\ threadStates[t] = "holding"
    /\ pc' = [pc EXCEPT ![t] = "Release"]
    /\ UNCHANGED <<lockState, threadStates, guardStates, spinning, acquisitionOrder>>

ReleaseLock(t) ==
    /\ pc[t] = "Release"
    /\ threadStates[t] = "holding"
    /\ AtomicStore(FALSE)
    /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
    /\ guardStates' = [guardStates EXCEPT ![t] = "none"]
    /\ spinning' = [spinning EXCEPT ![t] = 0]
    /\ pc' = [pc EXCEPT ![t] = "Done"]
    /\ UNCHANGED acquisitionOrder

TryLockOperation(t) ==
    /\ pc[t] = "Init"
    /\ threadStates[t] = "idle"
    /\ guardStates' = [guardStates EXCEPT ![t] = "PreemptDisabled"]
    /\ LET success == CompareAndSwap(FALSE, TRUE)
       IN IF success
          THEN /\ threadStates' = [threadStates EXCEPT ![t] = "holding"]
               /\ pc' = [pc EXCEPT ![t] = "Critical"]
               /\ acquisitionOrder' = Append(acquisitionOrder, t)
               /\ UNCHANGED spinning
          ELSE /\ threadStates' = [threadStates EXCEPT ![t] = "idle"]
               /\ guardStates' = [guardStates EXCEPT ![t] = "none"]
               /\ pc' = [pc EXCEPT ![t] = "Done"]
               /\ UNCHANGED <<spinning, acquisitionOrder>>

DisableIrq(t) ==
    /\ guardStates[t] = "PreemptDisabled"
    /\ guardStates' = [guardStates EXCEPT ![t] = "LocalIrqDisabled"]
    /\ UNCHANGED <<lockState, threadStates, spinning, acquisitionOrder, pc>>

Next ==
    \E t \in Threads:
        \/ StartLock(t)
        \/ TryAcquireLock(t)
        \/ SpinWait(t)
        \/ AcquiredLock(t)
        \/ CriticalSection(t)
        \/ ReleaseLock(t)
        \/ TryLockOperation(t)
        \/ DisableIrq(t)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    Cardinality({t \in Threads : threadStates[t] = "holding"}) <= 1

LockConsistency ==
    lockState = TRUE <=> \E t \in Threads : threadStates[t] = "holding"

NoDeadlock ==
    (\A t \in Threads : threadStates[t] \in {"idle", "spinning"}) =>
    (\E t \in Threads : ENABLED StartLock(t) \/ ENABLED TryAcquireLock(t))

EventualProgress ==
    \A t \in Threads : 
        (threadStates[t] = "spinning" /\ spinning[t] < MaxSpins) ~> 
        (threadStates[t] \in {"holding", "idle"})

GuardConsistency ==
    \A t \in Threads :
        threadStates[t] = "holding" => guardStates[t] \in {"PreemptDisabled", "LocalIrqDisabled"}

SpinBound ==
    \A t \in Threads : spinning[t] <= MaxSpins

AcquisitionFairness ==
    \A t \in Threads :
        threadStates[t] = "spinning" ~> threadStates[t] = "holding"

====