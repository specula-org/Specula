---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Procs

ASSUME Procs = {"p1", "p2", "p3"}

PCStates    == {"idle", "acq_read", "wait_read", "reading", "acq_write", "wait_write", "writing", "acq_upread", "wait_upread", "upreading", "upgrading"}
LockTypes   == {"none", "read", "write", "upread"}

VARIABLES
    lock_state,
    wait_queue,
    pc,
    lock_holders

vars == <<lock_state, wait_queue, pc, lock_holders>>

TypeOK ==
    /\ lock_state \in [writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: Nat]
    /\ wait_queue \in Seq(Procs)
    /\ pc \in [Procs -> PCStates]
    /\ lock_holders \in [Procs -> LockTypes]

Init ==
    /\ lock_state = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ wait_queue = <<>>
    /\ pc = [p \in Procs |-> "idle"]
    /\ lock_holders = [p \in Procs |-> "none"]

IsLockFreeForRead(ls) == ~ls.writer /\ ~ls.upgrading
IsLockFreeForWrite(ls) == ~ls.writer /\ ~ls.upreader /\ ls.readers = 0
IsLockFreeForUpRead(ls) == ~ls.writer /\ ~ls.upreader
CanUpgrade(ls) == ls.readers = 0

WokenPC(st) ==
    CASE st = "wait_read"   -> "acq_read"
      [] st = "wait_write"  -> "acq_write"
      [] st = "wait_upread" -> "acq_upread"

RequestRead(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "acq_read"]
    /\ UNCHANGED <<lock_state, wait_queue, lock_holders>>

TryAcquireRead(p) ==
    /\ pc[p] = "acq_read"
    /\ IF IsLockFreeForRead(lock_state) THEN
        /\ lock_state' = [lock_state EXCEPT !.readers = lock_state.readers + 1]
        /\ pc' = [pc EXCEPT ![p] = "reading"]
        /\ lock_holders' = [lock_holders EXCEPT ![p] = "read"]
        /\ UNCHANGED wait_queue
    ELSE
        /\ pc' = [pc EXCEPT ![p] = "wait_read"]
        /\ wait_queue' = Append(wait_queue, p)
        /\ UNCHANGED <<lock_state, lock_holders>>

ReleaseRead(p) ==
    /\ pc[p] = "reading"
    /\ lock_state' = [lock_state EXCEPT !.readers = lock_state.readers - 1]
    /\ lock_holders' = [lock_holders EXCEPT ![p] = "none"]
    /\ IF lock_state.readers = 1 /\ Len(wait_queue) > 0 THEN
        /\ LET woken == Head(wait_queue) IN
           /\ wait_queue' = Tail(wait_queue)
           /\ pc' = [pc EXCEPT ![p] = "idle", ![woken] = WokenPC(pc[woken])]
    ELSE
        /\ UNCHANGED wait_queue
        /\ pc' = [pc EXCEPT ![p] = "idle"]

RequestWrite(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "acq_write"]
    /\ UNCHANGED <<lock_state, wait_queue, lock_holders>>

TryAcquireWrite(p) ==
    /\ pc[p] = "acq_write"
    /\ IF IsLockFreeForWrite(lock_state) THEN
        /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
        /\ pc' = [pc EXCEPT ![p] = "writing"]
        /\ lock_holders' = [lock_holders EXCEPT ![p] = "write"]
        /\ UNCHANGED wait_queue
    ELSE
        /\ pc' = [pc EXCEPT ![p] = "wait_write"]
        /\ wait_queue' = Append(wait_queue, p)
        /\ UNCHANGED <<lock_state, lock_holders>>

ReleaseWrite(p) ==
    /\ pc[p] = "writing"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ lock_holders' = [lock_holders EXCEPT ![p] = "none"]
    /\ LET woken_procs == AsSet(wait_queue) IN
       /\ wait_queue' = <<>>
       /\ pc' = [q \in Procs |-> IF q = p THEN "idle" ELSE IF q \in woken_procs THEN WokenPC(pc[q]) ELSE pc[q]]

RequestUpRead(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "acq_upread"]
    /\ UNCHANGED <<lock_state, wait_queue, lock_holders>>

TryAcquireUpRead(p) ==
    /\ pc[p] = "acq_upread"
    /\ IF IsLockFreeForUpRead(lock_state) THEN
        /\ lock_state' = [lock_state EXCEPT !.upreader = TRUE]
        /\ pc' = [pc EXCEPT ![p] = "upreading"]
        /\ lock_holders' = [lock_holders EXCEPT ![p] = "upread"]
        /\ UNCHANGED wait_queue
    ELSE
        /\ pc' = [pc EXCEPT ![p] = "wait_upread"]
        /\ wait_queue' = Append(wait_queue, p)
        /\ UNCHANGED <<lock_state, lock_holders>>

ReleaseUpRead(p) ==
    /\ pc[p] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !.upreader = FALSE]
    /\ lock_holders' = [lock_holders EXCEPT ![p] = "none"]
    /\ IF lock_state.readers = 0 THEN
        /\ LET woken_procs == AsSet(wait_queue) IN
           /\ wait_queue' = <<>>
           /\ pc' = [q \in Procs |-> IF q = p THEN "idle" ELSE IF q \in woken_procs THEN WokenPC(pc[q]) ELSE pc[q]]
    ELSE
        /\ UNCHANGED wait_queue
        /\ pc' = [pc EXCEPT ![p] = "idle"]

StartUpgrade(p) ==
    /\ pc[p] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "upgrading"]
    /\ UNCHANGED <<wait_queue, lock_holders>>

TryUpgrade(p) ==
    /\ pc[p] = "upgrading"
    /\ CanUpgrade(lock_state)
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.upreader = FALSE, !.upgrading = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "writing"]
    /\ lock_holders' = [lock_holders EXCEPT ![p] = "write"]
    /\ UNCHANGED wait_queue

Downgrade(p) ==
    /\ pc[p] = "writing"
    /\ lock_holders[p] = "write"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upreader = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "upreading"]
    /\ lock_holders' = [lock_holders EXCEPT ![p] = "upread"]
    /\ UNCHANGED wait_queue

ProcActions(p) ==
    \/ RequestRead(p)
    \/ TryAcquireRead(p)
    \/ ReleaseRead(p)
    \/ RequestWrite(p)
    \/ TryAcquireWrite(p)
    \/ ReleaseWrite(p)
    \/ RequestUpRead(p)
    \/ TryAcquireUpRead(p)
    \/ ReleaseUpRead(p)
    \/ StartUpgrade(p)
    \/ TryUpgrade(p)
    \/ Downgrade(p)

Next == \E p \in Procs: ProcActions(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
