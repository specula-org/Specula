---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS ProcSet

VARIABLES lock, p_state, wait_queue

vars == <<lock, p_state, wait_queue>>

Init ==
    /\ lock = [writer |-> FALSE, upgradable |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ p_state = [p \in ProcSet |-> "idle"]
    /\ wait_queue = <<>>

\* Reader Actions
TryAcquireRead(p) ==
    /\ p_state[p] = "idle"
    /\ ~lock.writer /\ ~lock.upgrading
    /\ lock' = [lock EXCEPT !.readers = @ + 1]
    /\ p_state' = [p_state EXCEPT ![p] = "reading"]
    /\ UNCHANGED wait_queue

BlockOnRead(p) ==
    /\ p_state[p] = "idle"
    /\ lock.writer \/ lock.upgrading
    /\ p_state' = [p_state EXCEPT ![p] = "waiting"]
    /\ wait_queue' = Append(wait_queue, [proc |-> p, type |-> "read"])
    /\ UNCHANGED lock

ReleaseRead(p) ==
    /\ p_state[p] = "reading"
    /\ LET new_lock == [lock EXCEPT !.readers = @ - 1]
       IN /\ lock' = new_lock
          /\ IF lock.readers = 1 /\ Len(wait_queue) > 0 THEN
                LET woken_proc == Head(wait_queue).proc
                IN /\ wait_queue' = Tail(wait_queue)
                   /\ p_state' = [p_state EXCEPT ![p] = "idle", ![woken_proc] = "idle"]
             ELSE
                /\ wait_queue' = wait_queue
                /\ p_state' = [p_state EXCEPT ![p] = "idle"]

\* Writer Actions
TryAcquireWrite(p) ==
    /\ p_state[p] = "idle"
    /\ lock.writer = FALSE /\ lock.upgradable = FALSE /\ lock.upgrading = FALSE /\ lock.readers = 0
    /\ lock' = [lock EXCEPT !.writer = TRUE]
    /\ p_state' = [p_state EXCEPT ![p] = "writing"]
    /\ UNCHANGED wait_queue

BlockOnWrite(p) ==
    /\ p_state[p] = "idle"
    /\ (lock.writer \/ lock.upgradable \/ lock.upgrading \/ lock.readers > 0)
    /\ p_state' = [p_state EXCEPT ![p] = "waiting"]
    /\ wait_queue' = Append(wait_queue, [proc |-> p, type |-> "write"])
    /\ UNCHANGED lock

ReleaseWrite(p) ==
    /\ p_state[p] = "writing"
    /\ lock' = [lock EXCEPT !.writer = FALSE]
    /\ LET waiting_procs == {q.proc : q \in SeqToSet(wait_queue)}
       IN p_state' = [q \in ProcSet |-> IF q \in waiting_procs \cup {p} THEN "idle" ELSE p_state[q]]
    /\ wait_queue' = <<>>

\* Upgradeable Reader Actions
TryAcquireUpRead(p) ==
    /\ p_state[p] = "idle"
    /\ ~lock.writer /\ ~lock.upgradable
    /\ lock' = [lock EXCEPT !.upgradable = TRUE]
    /\ p_state' = [p_state EXCEPT ![p] = "upreading"]
    /\ UNCHANGED wait_queue

BlockOnUpRead(p) ==
    /\ p_state[p] = "idle"
    /\ lock.writer \/ lock.upgradable
    /\ p_state' = [p_state EXCEPT ![p] = "waiting"]
    /\ wait_queue' = Append(wait_queue, [proc |-> p, type |-> "upread"])
    /\ UNCHANGED lock

ReleaseUpRead(p) ==
    /\ p_state[p] = "upreading"
    /\ LET new_lock == [lock EXCEPT !.upgradable = FALSE]
       IN /\ lock' = new_lock
          /\ IF new_lock.readers = 0 /\ ~new_lock.writer /\ ~new_lock.upgrading THEN
                LET waiting_procs == {q.proc : q \in SeqToSet(wait_queue)}
                IN /\ p_state' = [q \in ProcSet |-> IF q \in waiting_procs \cup {p} THEN "idle" ELSE p_state[q]]
                   /\ wait_queue' = <<>>
             ELSE
                /\ p_state' = [p_state EXCEPT ![p] = "idle"]
                /\ UNCHANGED wait_queue

\* Upgrade/Downgrade Actions
BeginUpgrade(p) ==
    /\ p_state[p] = "upreading"
    /\ lock' = [lock EXCEPT !.upgrading = TRUE]
    /\ p_state' = [p_state EXCEPT ![p] = "upgrading"]
    /\ UNCHANGED wait_queue

CompleteUpgrade(p) ==
    /\ p_state[p] = "upgrading"
    /\ lock.readers = 0
    /\ lock' = [lock EXCEPT !.writer = TRUE, !.upgradable = FALSE, !.upgrading = FALSE]
    /\ p_state' = [p_state EXCEPT ![p] = "writing"]
    /\ UNCHANGED wait_queue

Downgrade(p) ==
    /\ p_state[p] = "writing"
    /\ lock' = [lock EXCEPT !.writer = FALSE, !.upgradable = TRUE]
    /\ p_state' = [p_state EXCEPT ![p] = "upreading"]
    /\ UNCHANGED wait_queue

Next ==
    \/ \E p \in ProcSet:
        \/ TryAcquireRead(p)
        \/ BlockOnRead(p)
        \/ ReleaseRead(p)
        \/ TryAcquireWrite(p)
        \/ BlockOnWrite(p)
        \/ ReleaseWrite(p)
        \/ TryAcquireUpRead(p)
        \/ BlockOnUpRead(p)
        \/ ReleaseUpRead(p)
        \/ BeginUpgrade(p)
        \/ CompleteUpgrade(p)
        \/ Downgrade(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
