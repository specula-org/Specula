---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES lock_state, wait_queue, thread_state

vars == <<lock_state, wait_queue, thread_state>>

ThreadStates == {"idle", "waiting", "reading", "writing", "upreading", "upgrading"}
LockStateRecord == [writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: Nat]

TypeOK ==
    /\ lock_state \in LockStateRecord
    /\ wait_queue \in Seq(Threads)
    /\ thread_state \in [Threads -> ThreadStates]
    /\ IsFiniteSet(Threads)

Init ==
    /\ lock_state = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ wait_queue = <<>>
    /\ thread_state = [t \in Threads |-> "idle"]

(* Actions for acquiring read lock *)
AcquireRead(t) ==
    /\ thread_state[t] = "idle"
    /\ IF \lnot lock_state.writer /\ \lnot lock_state.upgrading
       THEN /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
            /\ thread_state' = [thread_state EXCEPT ![t] = "reading"]
            /\ UNCHANGED <<wait_queue>>
       ELSE /\ wait_queue' = Append(wait_queue, t)
            /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
            /\ UNCHANGED <<lock_state>>

(* Action for releasing read lock *)
ReleaseRead(t) ==
    /\ thread_state[t] = "reading"
    /\ lock_state' = [lock_state EXCEPT !.readers = @ - 1]
    /\ IF lock_state.readers - 1 = 0 /\ Len(wait_queue) > 0
       THEN /\ wait_queue' = Tail(wait_queue)
            /\ thread_state' = [thread_state EXCEPT ![t] = "idle", ![Head(wait_queue)] = "idle"]
       ELSE /\ UNCHANGED <<wait_queue>>
            /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]

(* Actions for acquiring write lock *)
AcquireWrite(t) ==
    /\ thread_state[t] = "idle"
    /\ IF lock_state = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
       THEN /\ lock_state' = [lock_state EXCEPT !.writer = TRUE]
            /\ thread_state' = [thread_state EXCEPT ![t] = "writing"]
            /\ UNCHANGED <<wait_queue>>
       ELSE /\ wait_queue' = Append(wait_queue, t)
            /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
            /\ UNCHANGED <<lock_state>>

(* Action for releasing write lock *)
ReleaseWrite(t) ==
    /\ thread_state[t] = "writing"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE]
    /\ wait_queue' = <<>>
    /\ thread_state' = [ th \in Threads |->
                          IF th = t \/ th \in Range(wait_queue) THEN "idle"
                          ELSE thread_state[th] ]

(* Actions for acquiring upgradeable read lock *)
AcquireUpRead(t) ==
    /\ thread_state[t] = "idle"
    /\ IF \lnot lock_state.writer /\ \lnot lock_state.upreader
       THEN /\ lock_state' = [lock_state EXCEPT !.upreader = TRUE]
            /\ thread_state' = [thread_state EXCEPT ![t] = "upreading"]
            /\ UNCHANGED <<wait_queue>>
       ELSE /\ wait_queue' = Append(wait_queue, t)
            /\ thread_state' = [thread_state EXCEPT ![t] = "waiting"]
            /\ UNCHANGED <<lock_state>>

(* Action for releasing upgradeable read lock *)
ReleaseUpRead(t) ==
    /\ thread_state[t] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !.upreader = FALSE]
    /\ IF lock_state.readers = 0
       THEN /\ wait_queue' = <<>>
            /\ thread_state' = [ th \in Threads |->
                                   IF th = t \/ th \in Range(wait_queue) THEN "idle"
                                   ELSE thread_state[th] ]
       ELSE /\ UNCHANGED <<wait_queue>>
            /\ thread_state' = [thread_state EXCEPT ![t] = "idle"]

(* Action for starting the upgrade process *)
StartUpgrade(t) ==
    /\ thread_state[t] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]
    /\ thread_state' = [thread_state EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED <<wait_queue>>

(* Action for completing the upgrade when no readers are present *)
CompleteUpgrade(t) ==
    /\ thread_state[t] = "upgrading"
    /\ lock_state.readers = 0
    /\ lock_state' = [lock_state EXCEPT !.writer = TRUE, !.upreader = FALSE, !.upgrading = FALSE]
    /\ thread_state' = [thread_state EXCEPT ![t] = "writing"]
    /\ UNCHANGED <<wait_queue>>

(* Action for downgrading a write lock to an upgradeable read lock *)
Downgrade(t) ==
    /\ thread_state[t] = "writing"
    /\ lock_state' = [lock_state EXCEPT !.writer = FALSE, !.upreader = TRUE]
    /\ thread_state' = [thread_state EXCEPT ![t] = "upreading"]
    /\ UNCHANGED <<wait_queue>>

Next ==
    \E t \in Threads:
        \/ AcquireRead(t)
        \/ ReleaseRead(t)
        \/ AcquireWrite(t)
        \/ ReleaseWrite(t)
        \/ AcquireUpRead(t)
        \/ ReleaseUpRead(t)
        \/ StartUpgrade(t)
        \/ CompleteUpgrade(t)
        \/ Downgrade(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====