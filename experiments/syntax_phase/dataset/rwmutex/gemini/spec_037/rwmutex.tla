---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Threads

ASSUME Threads = { "t1", "t2", "t3" }

VARIABLES
    lock_state,
    thread_state,
    wait_queue

vars == << lock_state, thread_state, wait_queue >>

TypeOK ==
    /\ lock_state \in [writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: Nat]
    /\ thread_state \in [Threads -> {"idle", "req_read", "req_write", "req_upread",
                                     "reading", "writing", "upreading", "upgrading"}]
    /\ wait_queue \in Seq(Threads)

Init ==
    /\ lock_state = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ thread_state = [t \in Threads |-> "idle"]
    /\ wait_queue = << >>

CanAcquireRead ==
    /\ lock_state["writer"] = FALSE
    /\ lock_state["upgrading"] = FALSE

CanAcquireWrite ==
    /\ lock_state["writer"] = FALSE
    /\ lock_state["upreader"] = FALSE
    /\ lock_state["readers"] = 0

CanAcquireUpread ==
    /\ lock_state["writer"] = FALSE
    /\ lock_state["upreader"] = FALSE

RequestRead(p) ==
    /\ thread_state[p] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![p] = "req_read"]
    /\ UNCHANGED << lock_state, wait_queue >>

RequestWrite(p) ==
    /\ thread_state[p] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![p] = "req_write"]
    /\ UNCHANGED << lock_state, wait_queue >>

RequestUpread(p) ==
    /\ thread_state[p] = "idle"
    /\ thread_state' = [thread_state EXCEPT ![p] = "req_upread"]
    /\ UNCHANGED << lock_state, wait_queue >>

AcquireRead(p) ==
    /\ thread_state[p] = "req_read"
    /\ p \notin Elems(wait_queue)
    /\ CanAcquireRead
    /\ lock_state' = [lock_state EXCEPT !["readers"] = lock_state["readers"] + 1]
    /\ thread_state' = [thread_state EXCEPT ![p] = "reading"]
    /\ UNCHANGED << wait_queue >>

AcquireWrite(p) ==
    /\ thread_state[p] = "req_write"
    /\ p \notin Elems(wait_queue)
    /\ CanAcquireWrite
    /\ lock_state' = [lock_state EXCEPT !["writer"] = TRUE]
    /\ thread_state' = [thread_state EXCEPT ![p] = "writing"]
    /\ UNCHANGED << wait_queue >>

AcquireUpread(p) ==
    /\ thread_state[p] = "req_upread"
    /\ p \notin Elems(wait_queue)
    /\ CanAcquireUpread
    /\ lock_state' = [lock_state EXCEPT !["upreader"] = TRUE]
    /\ thread_state' = [thread_state EXCEPT ![p] = "upreading"]
    /\ UNCHANGED << wait_queue >>

Block(p) ==
    /\ p \notin Elems(wait_queue)
    /\ \/ (thread_state[p] = "req_read" /\ ~CanAcquireRead)
       \/ (thread_state[p] = "req_write" /\ ~CanAcquireWrite)
       \/ (thread_state[p] = "req_upread" /\ ~CanAcquireUpread)
    /\ wait_queue' = Append(wait_queue, p)
    /\ UNCHANGED << lock_state, thread_state >>

ReleaseRead(p) ==
    /\ thread_state[p] = "reading"
    /\ LET new_readers == lock_state["readers"] - 1 IN
       /\ lock_state' = [lock_state EXCEPT !["readers"] = new_readers]
       /\ IF new_readers = 0 /\ Len(wait_queue) > 0 THEN
            wait_queue' = Tail(wait_queue)
          ELSE
            wait_queue' = wait_queue
    /\ thread_state' = [thread_state EXCEPT ![p] = "idle"]

ReleaseWrite(p) ==
    /\ thread_state[p] = "writing"
    /\ lock_state' = [lock_state EXCEPT !["writer"] = FALSE]
    /\ thread_state' = [thread_state EXCEPT ![p] = "idle"]
    /\ wait_queue' = << >>

ReleaseUpread(p) ==
    /\ thread_state[p] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !["upreader"] = FALSE]
    /\ thread_state' = [thread_state EXCEPT ![p] = "idle"]
    /\ IF lock_state["readers"] = 0 THEN
         wait_queue' = << >>
       ELSE
         wait_queue' = wait_queue

StartUpgrade(p) ==
    /\ thread_state[p] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !["upgrading"] = TRUE]
    /\ thread_state' = [thread_state EXCEPT ![p] = "upgrading"]
    /\ UNCHANGED << wait_queue >>

CompleteUpgrade(p) ==
    /\ thread_state[p] = "upgrading"
    /\ lock_state["readers"] = 0
    /\ lock_state' = [lock_state EXCEPT !["writer"] = TRUE, !["upreader"] = FALSE, !["upgrading"] = FALSE]
    /\ thread_state' = [thread_state EXCEPT ![p] = "writing"]
    /\ UNCHANGED << wait_queue >>

Downgrade(p) ==
    /\ thread_state[p] = "writing"
    /\ lock_state' = [lock_state EXCEPT !["writer"] = FALSE, !["upreader"] = TRUE]
    /\ thread_state' = [thread_state EXCEPT ![p] = "upreading"]
    /\ UNCHANGED << wait_queue >>

Next ==
    \E p \in Threads:
        \/ RequestRead(p)
        \/ RequestWrite(p)
        \/ RequestUpread(p)
        \/ AcquireRead(p)
        \/ AcquireWrite(p)
        \/ AcquireUpread(p)
        \/ Block(p)
        \/ ReleaseRead(p)
        \/ ReleaseWrite(p)
        \/ ReleaseUpread(p)
        \/ StartUpgrade(p)
        \/ CompleteUpgrade(p)
        \/ Downgrade(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Threads : WF_vars(
                           \/ ReleaseRead(p)
                           \/ ReleaseWrite(p)
                           \/ ReleaseUpread(p)
                           \/ Downgrade(p)
                           \/ CompleteUpgrade(p)
                         )

====