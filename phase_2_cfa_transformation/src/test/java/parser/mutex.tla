------------------------------- MODULE mutex -------------------------------
EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals

CONSTANTS Threads, Mutexes, Value

VARIABLES lock, queue, val, guards

vars == <<lock, queue, val, guards>>

MutexNew(mtx, initial_val) ==
    /\ lock' = [lock EXCEPT ![mtx] = FALSE]
    /\ queue' = [queue EXCEPT ![mtx] = <<>>]
    /\ val' = [val EXCEPT ![mtx] = initial_val]
    /\ UNCHANGED guards

\* lock
AcquireLock(mtx) ==
    LET attempt == lock[mtx] = FALSE
    IN
        IF attempt THEN 
            /\ lock' = [lock EXCEPT ![mtx] = TRUE]
            ELSE 
            /\ UNCHANGED lock

\* lock
ReleaseLock(mtx) ==
    lock' = [lock EXCEPT ![mtx] = FALSE]

MutexLock(mtx, t) ==
    /\ AcquireLock(mtx)
    /\ queue' = [queue EXCEPT ![mtx] = Append(@, t)]
    /\ guards' = guards \cup {[type |-> "MutexGuard", mutex |-> mtx]}
    /\ UNCHANGED <<val>>

MutexUnlock(self) == 
    LET mtx == self IN 
        /\ IF Len(queue[mtx]) > 0 THEN 
            LET next_thread == Head(queue[mtx]) IN 
                /\ queue' = [queue EXCEPT ![mtx] = Tail(@)] 
                /\ lock' = [lock EXCEPT ![mtx] = TRUE] 
            ELSE 
                /\ ReleaseLock(mtx) 
                \* /\ UNCHANGED <<queue>> 
        /\ guards' = guards \ {[type |-> "MutexGuard", mutex |-> self]}
        /\ UNCHANGED <<val>>

MutexTryLock(self) ==
    /\ AcquireLock(self)
    /\ guards' = guards \cup {[type |-> "MutexGuard", mutex |-> self]}
    /\ UNCHANGED <<val, queue>>

MutexGuardDrop(guard) ==
    LET mtx == guard.mutex
    IN
        /\ IF Len(queue[mtx]) > 0 THEN 
            LET next_thread == Head(queue[mtx]) IN
                /\ queue' = [queue EXCEPT ![mtx] = Tail(@)]
                /\ lock' = [lock EXCEPT ![mtx] = TRUE]
            ELSE 
            /\ UNCHANGED <<queue>>
            /\ ReleaseLock(mtx)
        /\ guards' = guards \ {guard}
        /\ UNCHANGED <<val>>

Init == 
    /\ lock = [m \in Mutexes |-> FALSE]
    /\ queue = [m \in Mutexes |-> <<>>]
    /\ val = [m \in Mutexes |-> 0]
    /\ guards = {}

Next == 
    \/ \E mtx \in Mutexes: \E t \in Threads: MutexLock(mtx, t)
    \/ \E mtx \in Mutexes: MutexUnlock(mtx)
    \/ \E mtx \in Mutexes:
        \/ MutexTryLock(mtx)
        \/ /\ ReleaseLock(mtx)
           /\ UNCHANGED <<queue, val, guards>>
        \/ /\ AcquireLock(mtx)
           /\ UNCHANGED <<queue, val, guards>>
    \/ \E guard \in guards:
        \/ MutexGuardDrop(guard)
    \/ \E mtx \in Mutexes: \E v \in Value:
        \/ MutexNew(mtx, v)
        
\* TypeInvariant ==
\*     /\ lock \in [Mutexes -> BOOLEAN]
\*     /\ queue \in [Mutexes -> Seq(Threads)]
\*     /\ guards \subseteq {[type |-> "MutexGuard", mutex: Mutexes]}

Spec == Init /\ [][Next]_(vars)

=============================================================================