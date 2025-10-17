---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads
ASSUME Threads \subseteq {"t1", "t2", "t3"}

(* --- State Variables --- *)
vars lock_state,  \* [writer: BOOL, upreader: BOOL, upgrading: BOOL, readers: Nat]
     wait_queue,  \* Seq(Threads), FIFO queue of waiting threads
     pc           \* [Threads -> PCStates]

PCStates == {"idle", "reading", "writing", "upreading", "upgrading",
             "waiting_read", "waiting_write", "waiting_upread"}

vars_tuple == <<lock_state, wait_queue, pc>>

(* --- Type Invariant --- *)
TypeOK ==
    /\ lock_state \in [writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: Nat]
    /\ wait_queue \in Seq(Threads)
    /\ pc \in [Threads -> PCStates]
    /\ NoDuplicates(wait_queue)
    /\ \A t \in Threads: (t \in Ran(wait_queue)) <=> (pc[t] \in {"waiting_read", "waiting_write", "waiting_upread"})

(* --- Initial State --- *)
Init ==
    /\ lock_state = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ wait_queue = <<>>
    /\ pc = [t \in Threads |-> "idle"]

(* --- Helper Operators for Lock State --- *)
CanRead(ls) == \lnot ls.writer /\ \lnot ls.upgrading
CanWrite(ls) == \lnot ls.writer /\ \lnot ls.upreader /\ ls.readers = 0
CanUpread(ls) == \lnot ls.writer /\ \lnot ls.upreader
CanCompleteUpgrade(ls) == ls.readers = 0

(* --- Actions --- *)

(* A thread requests a read lock. It's either granted or the thread waits. *)
RequestRead(self) ==
    /\ pc[self] = "idle"
    /\ IF CanRead(lock_state)
       THEN /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
            /\ pc' = [pc EXCEPT ![self] = "reading"]
            /\ UNCHANGED wait_queue
       ELSE /\ pc' = [pc EXCEPT ![self] = "waiting_read"]
            /\ wait_queue' = Append(wait_queue, self)
            /\ UNCHANGED lock_state

(* A thread requests a write lock. *)
RequestWrite(self) ==
    /\ pc[self] = "idle"
    /\ IF CanWrite(lock_state)
       THEN /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "writing"]
            /\ UNCHANGED wait_queue
       ELSE /\ pc' = [pc EXCEPT ![self] = "waiting_write"]
            /\ wait_queue' = Append(wait_queue, self)
            /\ UNCHANGED lock_state

(* A thread requests an upgradeable read lock. *)
RequestUpread(self) ==
    /\ pc[self] = "idle"
    /\ IF CanUpread(lock_state)
       THEN /\ lock_state' = [lock_state EXCEPT !.upreader = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "upreading"]
            /\ UNCHANGED wait_queue
       ELSE /\ pc' = [pc EXCEPT ![self] = "waiting_upread"]
            /\ wait_queue' = Append(wait_queue, self)
            /\ UNCHANGED lock_state

(* A waiting thread is granted the lock. This models being woken and successfully
   re-evaluating the lock condition. The wake_all/wake_one distinction is
   abstracted by allowing any waiting thread to be processed, with fairness
   ensuring progress. *)
GrantWaitedLock(self) ==
    /\ pc[self] \in {"waiting_read", "waiting_write", "waiting_upread"}
    /\ \/ /\ pc[self] = "waiting_read"
          /\ CanRead(lock_state)
          /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
          /\ pc' = [pc EXCEPT ![self] = "reading"]
       \/ /\ pc[self] = "waiting_write"
          /\ CanWrite(lock_state)
          /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
          /\ pc' = [pc EXCEPT ![self] = "writing"]
       \/ /\ pc[self] = "waiting_upread"
          /\ CanUpread(lock_state)
          /\ lock_state' = [lock_state EXCEPT !.upreader = TRUE]
          /\ pc' = [pc EXCEPT ![self] = "upreading"]
    /\ wait_queue' = RemoveEl(wait_queue, self)

(* A thread releases its read lock. *)
ReleaseRead(self) ==
    /\ pc[self] = "reading"
    /\ lock_state' = [lock_state EXCEPT !.readers = @ - 1]
    /\ pc' = [pc EXCEPT ![self] = "idle"]
    /\ UNCHANGED wait_queue

(* A thread releases its write lock. *)
ReleaseWrite(self) ==
    /\ pc[self] = "writing"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "idle"]
    /\ UNCHANGED wait_queue

(* A thread releases its upgradeable read lock. *)
ReleaseUpread(self) ==
    /\ pc[self] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !.upreader = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "idle"]
    /\ UNCHANGED wait_queue

(* An upgradeable reader starts the upgrade process. *)
StartUpgrade(self) ==
    /\ pc[self] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "upgrading"]
    /\ UNCHANGED wait_queue

(* An upgrading thread completes the upgrade to a writer. *)
CompleteUpgrade(self) ==
    /\ pc[self] = "upgrading"
    /\ CanCompleteUpgrade(lock_state)
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.upreader = FALSE, !.upgrading = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "writing"]
    /\ UNCHANGED wait_queue

(* A writer downgrades to an upgradeable reader. *)
Downgrade(self) ==
    /\ pc[self] = "writing"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upreader = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "upreading"]
    /\ UNCHANGED wait_queue

(* --- Next State Relation --- *)
Next ==
    \E self \in Threads:
        \/ RequestRead(self)
        \/ RequestWrite(self)
        \/ RequestUpread(self)
        \/ GrantWaitedLock(self)
        \/ ReleaseRead(self)
        \/ ReleaseWrite(self)
        \/ ReleaseUpread(self)
        \/ StartUpgrade(self)
        \/ CompleteUpgrade(self)
        \/ Downgrade(self)

(* --- Specification --- *)
Spec == Init /\ [][Next]_vars_tuple /\ \A self \in Threads : WF_vars_tuple(GrantWaitedLock(self))

====