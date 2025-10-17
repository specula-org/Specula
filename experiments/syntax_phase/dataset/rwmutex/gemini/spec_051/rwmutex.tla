---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Procs

VARIABLES
    lock_readers,
    lock_writer,
    lock_up_reader,
    lock_upgrading,
    pc,
    wait_queue,
    waiting_for

vars == <<lock_readers, lock_writer, lock_up_reader, lock_upgrading, pc, wait_queue, waiting_for>>

TypeOK ==
    /\ lock_readers \in Nat
    /\ lock_writer \in BOOLEAN
    /\ lock_up_reader \in BOOLEAN
    /\ lock_upgrading \in BOOLEAN
    /\ pc \in [Procs -> {{"idle", "req_read", "req_write", "req_upread", "reading", "writing", "up_reading", "upgrading", "blocked"}}]
    /\ wait_queue \in Seq(Procs)
    /\ waiting_for \in [Procs -> {{"read", "write", "upread", "none"}}]

Init ==
    /\ lock_readers = 0
    /\ lock_writer = FALSE
    /\ lock_up_reader = FALSE
    /\ lock_upgrading = FALSE
    /\ pc = [p \in Procs |-> "idle"]
    /\ wait_queue = <<>>
    /\ waiting_for = [p \in Procs |-> "none"]

(* A process in an idle state decides to request a lock *)
RequestLock(p) ==
    /\ pc[p] = "idle"
    /\ \/ pc' = [pc EXCEPT ![p] = "req_read"]
       \/ pc' = [pc EXCEPT ![p] = "req_write"]
       \/ pc' = [pc EXCEPT ![p] = "req_upread"]
    /\ UNCHANGED <<lock_readers, lock_writer, lock_up_reader, lock_upgrading, wait_queue, waiting_for>>

(* A process attempts to acquire a read lock. It succeeds if there is no writer and no upgrade in progress. Otherwise, it blocks. *)
AcquireReadOrBlock(p) ==
    /\ pc[p] = "req_read"
    /\ IF \lnot lock_writer /\ \lnot lock_upgrading
       THEN (* Success *)
            /\ lock_readers' = lock_readers + 1
            /\ pc' = [pc EXCEPT ![p] = "reading"]
            /\ UNCHANGED <<lock_writer, lock_up_reader, lock_upgrading, wait_queue, waiting_for>>
       ELSE (* Failure, so block *)
            /\ pc' = [pc EXCEPT ![p] = "blocked"]
            /\ wait_queue' = Append(wait_queue, p)
            /\ waiting_for' = [waiting_for EXCEPT ![p] = "read"]
            /\ UNCHANGED <<lock_readers, lock_writer, lock_up_reader, lock_upgrading>>

(* A process attempts to acquire a write lock. It succeeds only if the lock is completely free. Otherwise, it blocks. *)
AcquireWriteOrBlock(p) ==
    /\ pc[p] = "req_write"
    /\ IF \lnot lock_writer /\ \lnot lock_up_reader /\ lock_readers = 0
       THEN (* Success *)
            /\ lock_writer' = TRUE
            /\ pc' = [pc EXCEPT ![p] = "writing"]
            /\ UNCHANGED <<lock_readers, lock_up_reader, lock_upgrading, wait_queue, waiting_for>>
       ELSE (* Failure, so block *)
            /\ pc' = [pc EXCEPT ![p] = "blocked"]
            /\ wait_queue' = Append(wait_queue, p)
            /\ waiting_for' = [waiting_for EXCEPT ![p] = "write"]
            /\ UNCHANGED <<lock_readers, lock_writer, lock_up_reader, lock_upgrading>>

(* A process attempts to acquire an upgradeable read lock. It succeeds if there is no writer and no other upgradeable reader. Otherwise, it blocks. *)
AcquireUpReadOrBlock(p) ==
    /\ pc[p] = "req_upread"
    /\ IF \lnot lock_writer /\ \lnot lock_up_reader
       THEN (* Success *)
            /\ lock_up_reader' = TRUE
            /\ pc' = [pc EXCEPT ![p] = "up_reading"]
            /\ UNCHANGED <<lock_readers, lock_writer, lock_upgrading, wait_queue, waiting_for>>
       ELSE (* Failure, so block *)
            /\ pc' = [pc EXCEPT ![p] = "blocked"]
            /\ wait_queue' = Append(wait_queue, p)
            /\ waiting_for' = [waiting_for EXCEPT ![p] = "upread"]
            /\ UNCHANGED <<lock_readers, lock_writer, lock_up_reader, lock_upgrading>>

(* A process releases its read lock. If it was the last reader, it wakes one waiting process. *)
ReleaseRead(p) ==
    /\ pc[p] = "reading"
    /\ LET new_readers == lock_readers - 1
       IN /\ lock_readers' = new_readers
          /\ IF new_readers = 0 /\ Len(wait_queue) > 0
             THEN LET woken_p == Head(wait_queue)
                  IN /\ wait_queue' = Tail(wait_queue)
                     /\ pc' = [pc EXCEPT ![p] = "idle", ![woken_p] = "req_" \o waiting_for[woken_p]]
             ELSE /\ wait_queue' = wait_queue
                  /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lock_writer, lock_up_reader, lock_upgrading, waiting_for>>

(* A process releases its write lock and wakes all waiting processes. *)
ReleaseWrite(p) ==
    /\ pc[p] = "writing"
    /\ lock_writer' = FALSE
    /\ LET WokenProcs == SeqToSet(wait_queue)
       IN /\ pc' = [q \in Procs |-> CASE q = p -> "idle"
                                      [] q \in WokenProcs -> "req_" \o waiting_for[q]
                                      [] OTHER -> pc[q]]
          /\ wait_queue' = <<>>
    /\ UNCHANGED <<lock_readers, lock_up_reader, lock_upgrading, waiting_for>>

(* A process releases its upgradeable read lock. If the lock becomes completely free, it wakes all waiting processes. *)
ReleaseUpRead(p) ==
    /\ pc[p] = "up_reading"
    /\ lock_up_reader' = FALSE
    /\ IF \lnot lock_writer /\ lock_readers = 0
       THEN (* Lock becomes free, wake all *)
            LET WokenProcs == SeqToSet(wait_queue)
            IN /\ pc' = [q \in Procs |-> CASE q = p -> "idle"
                                           [] q \in WokenProcs -> "req_" \o waiting_for[q]
                                           [] OTHER -> pc[q]]
               /\ wait_queue' = <<>>
       ELSE (* Lock not free, do not wake *)
            /\ pc' = [pc EXCEPT ![p] = "idle"]
            /\ wait_queue' = wait_queue
    /\ UNCHANGED <<lock_readers, lock_writer, lock_upgrading, waiting_for>>

(* An upgradeable reader starts the upgrade process, setting the upgrading flag. *)
StartUpgrade(p) ==
    /\ pc[p] = "up_reading"
    /\ lock_upgrading' = TRUE
    /\ pc' = [pc EXCEPT ![p] = "upgrading"]
    /\ UNCHANGED <<lock_readers, lock_writer, lock_up_reader, wait_queue, waiting_for>>

(* An upgrading process completes the upgrade once all other readers are gone. *)
FinishUpgrade(p) ==
    /\ pc[p] = "upgrading"
    /\ lock_readers = 0
    /\ lock_writer' = TRUE
    /\ lock_up_reader' = FALSE
    /\ lock_upgrading' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ UNCHANGED <<lock_readers, wait_queue, waiting_for>>

(* A writer downgrades its lock to an upgradeable read lock. *)
Downgrade(p) ==
    /\ pc[p] = "writing"
    /\ lock_writer' = FALSE
    /\ lock_up_reader' = TRUE
    /\ pc' = [pc EXCEPT ![p] = "up_reading"]
    /\ UNCHANGED <<lock_readers, lock_upgrading, wait_queue, waiting_for>>

ProcessAction(p) ==
    \/ RequestLock(p)
    \/ AcquireReadOrBlock(p)
    \/ AcquireWriteOrBlock(p)
    \/ AcquireUpReadOrBlock(p)
    \/ ReleaseRead(p)
    \/ ReleaseWrite(p)
    \/ ReleaseUpRead(p)
    \/ StartUpgrade(p)
    \/ FinishUpgrade(p)
    \/ Downgrade(p)

Next == \E p \in Procs : ProcessAction(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
