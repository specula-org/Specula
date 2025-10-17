---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES lock_state, process_state, wait_queue

vars == <<lock_state, process_state, wait_queue>>

Init ==
    /\ lock_state = [ writer_active |-> FALSE,
                      upreader_active |-> FALSE,
                      upgrading |-> FALSE,
                      readers |-> 0 ]
    /\ process_state = [t \in Threads |-> "idle"]
    /\ wait_queue = <<>>

TryAcquireRead(t) ==
    /\ process_state[t] = "idle"
    /\ IF \lnot lock_state.writer_active /\ \lnot lock_state.upgrading
       THEN /\ lock_state' = [lock_state EXCEPT !.readers = @ + 1]
            /\ process_state' = [process_state EXCEPT ![t] = "reading"]
            /\ UNCHANGED wait_queue
       ELSE /\ process_state' = [process_state EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED lock_state

ReleaseRead(t) ==
    /\ process_state[t] = "reading"
    /\ LET new_readers == lock_state.readers - 1
       IN /\ lock_state' = [lock_state EXCEPT !.readers = new_readers]
          /\ IF lock_state.readers = 1 /\ Len(wait_queue) > 0
             THEN LET woken_t == Head(wait_queue)
                  IN /\ wait_queue' = Tail(wait_queue)
                     /\ process_state' = [process_state EXCEPT ![t] = "idle", ![woken_t] = "idle"]
             ELSE /\ wait_queue' = wait_queue
                  /\ process_state' = [process_state EXCEPT ![t] = "idle"]

TryAcquireWrite(t) ==
    /\ process_state[t] = "idle"
    /\ IF \lnot lock_state.writer_active /\ \lnot lock_state.upreader_active /\ lock_state.readers = 0
       THEN /\ lock_state' = [lock_state EXCEPT !.writer_active = TRUE]
            /\ process_state' = [process_state EXCEPT ![t] = "writing"]
            /\ UNCHANGED wait_queue
       ELSE /\ process_state' = [process_state EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED lock_state

ReleaseWrite(t) ==
    /\ process_state[t] = "writing"
    /\ lock_state' = [lock_state EXCEPT !.writer_active = FALSE]
    /\ LET WokenThreads == {wait_queue[i] : i \in 1..Len(wait_queue)}
       IN process_state' = [t_ \in Threads |-> IF t_ = t THEN "idle"
                                                ELSE IF t_ \in WokenThreads THEN "idle"
                                                ELSE process_state[t_]]
    /\ wait_queue' = <<>>

TryAcquireUpRead(t) ==
    /\ process_state[t] = "idle"
    /\ IF \lnot lock_state.writer_active /\ \lnot lock_state.upreader_active
       THEN /\ lock_state' = [lock_state EXCEPT !.upreader_active = TRUE]
            /\ process_state' = [process_state EXCEPT ![t] = "upreading"]
            /\ UNCHANGED wait_queue
       ELSE /\ process_state' = [process_state EXCEPT ![t] = "waiting"]
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED lock_state

ReleaseUpRead(t) ==
    /\ process_state[t] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !.upreader_active = FALSE]
    /\ LET WokenThreads == {wait_queue[i] : i \in 1..Len(wait_queue)}
       IN process_state' = [t_ \in Threads |-> IF t_ = t THEN "idle"
                                                ELSE IF t_ \in WokenThreads THEN "idle"
                                                ELSE process_state[t_]]
    /\ wait_queue' = <<>>

StartUpgrade(t) ==
    /\ process_state[t] = "upreading"
    /\ lock_state' = [lock_state EXCEPT !.upgrading = TRUE]
    /\ process_state' = [process_state EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED wait_queue

CompleteUpgrade(t) ==
    /\ process_state[t] = "upgrading"
    /\ lock_state.readers = 0
    /\ lock_state' = [lock_state EXCEPT !.upgrading = FALSE, !.writer_active = TRUE, !.upreader_active = FALSE]
    /\ process_state' = [process_state EXCEPT ![t] = "writing"]
    /\ UNCHANGED wait_queue

Downgrade(t) ==
    /\ process_state[t] = "writing"
    /\ lock_state.writer_active
    /\ \lnot lock_state.upreader_active
    /\ lock_state' = [lock_state EXCEPT !.writer_active = FALSE, !.upreader_active = TRUE]
    /\ process_state' = [process_state EXCEPT ![t] = "upreading"]
    /\ UNCHANGED wait_queue

Next == \E t \in Threads:
    \/ TryAcquireRead(t)
    \/ ReleaseRead(t)
    \/ TryAcquireWrite(t)
    \/ ReleaseWrite(t)
    \/ TryAcquireUpRead(t)
    \/ ReleaseUpRead(t)
    \/ StartUpgrade(t)
    \/ CompleteUpgrade(t)
    \/ Downgrade(t)

Fairness == \A t \in Threads:
    /\ WF_vars(TryAcquireRead(t))
    /\ WF_vars(ReleaseRead(t))
    /\ WF_vars(TryAcquireWrite(t))
    /\ WF_vars(ReleaseWrite(t))
    /\ WF_vars(TryAcquireUpRead(t))
    /\ WF_vars(ReleaseUpRead(t))
    /\ WF_vars(StartUpgrade(t))
    /\ WF_vars(CompleteUpgrade(t))
    /\ WF_vars(Downgrade(t))

Spec == Init /\ [][Next]_vars /\ Fairness

====