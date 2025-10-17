---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES locked, waitQueue, pc

Vars == <<locked, waitQueue, pc>>

PC_VALS == {"idle", "locking", "waiting", "critical"}

TypeOK ==
    /\ locked \in BOOLEAN
    /\ waitQueue \in Seq(Threads)
    /\ pc \in [Threads -> PC_VALS]

Init ==
    /\ locked = FALSE
    /\ waitQueue = <<>>
    /\ pc = [t \in Threads |-> "idle"]

(* A thread calls the non-blocking try_lock() *)
TryLock(t) ==
    /\ pc[t] = "idle"
    /\ IF \lnot locked THEN  (* Success *)
        /\ locked' = TRUE
        /\ pc' = [pc EXCEPT ![t] = "critical"]
        /\ UNCHANGED <<waitQueue>>
    ELSE  (* Failure *)
        /\ UNCHANGED Vars

(* A thread calls the blocking lock() *)
RequestBlockingLock(t) ==
    /\ pc[t] = "idle"
    /\ pc' = [pc EXCEPT ![t] = "locking"]
    /\ UNCHANGED <<locked, waitQueue>>

(* The core of wait_until(): attempt to acquire or block if busy *)
AcquireOrBlock(t) ==
    /\ pc[t] = "locking"
    /\ IF \lnot locked THEN  (* The try_lock() inside wait_until succeeds *)
        /\ locked' = TRUE
        /\ pc' = [pc EXCEPT ![t] = "critical"]
        /\ UNCHANGED <<waitQueue>>
    ELSE (* The try_lock() inside wait_until fails, so the thread blocks *)
        /\ pc' = [pc EXCEPT ![t] = "waiting"]
        /\ waitQueue' = Append(waitQueue, t)
        /\ UNCHANGED <<locked>>

(* A thread in the critical section unlocks (MutexGuard is dropped) *)
Unlock(t) ==
    /\ pc[t] = "critical"
    /\ locked' = FALSE
    /\ IF waitQueue = <<>> THEN
        /\ pc' = [pc EXCEPT ![t] = "idle"]
        /\ UNCHANGED <<waitQueue>>
    ELSE (* Wake one waiting thread in FIFO order *)
        /\ LET wokenThread == Head(waitQueue)
           IN /\ waitQueue' = Tail(waitQueue)
              /\ pc' = [pc EXCEPT ![t] = "idle", ![wokenThread] = "locking"]

Next ==
    \E t \in Threads:
        \/ TryLock(t)
        \/ RequestBlockingLock(t)
        \/ AcquireOrBlock(t)
        \/ Unlock(t)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====