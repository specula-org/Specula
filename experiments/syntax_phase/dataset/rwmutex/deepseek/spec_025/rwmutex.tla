---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, MaxReaders

VARIABLES lock, queue, guards, activeThreads

(* Type invariant *)
TypeOK == 
    /\ lock \in [writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: 0..MaxReaders]
    /\ queue \in Seq(Threads \times {"read", "write", "upread"})
    /\ guards \in SUBSET (Threads \times {"read", "write", "upread"})
    /\ activeThreads \in SUBSET Threads

(* Initial state *)
Init == 
    /\ lock = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ queue = <<>>
    /\ guards = {}
    /\ activeThreads = {}

(* Helper predicates *)
CanAcquireRead == 
    /\ ~lock.writer 
    /\ ~lock.upgrading

CanAcquireWrite == 
    /\ ~lock.writer 
    /\ ~lock.upreader 
    /\ lock.readers = 0

CanAcquireUpread == 
    /\ ~lock.writer 
    /\ ~lock.upreader

CanUpgrade == 
    /\ lock.upreader 
    /\ ~lock.writer 
    /\ lock.readers = 0

(* Core operations *)
AcquireRead(t) == 
    /\ t \notin activeThreads
    /\ IF CanAcquireRead 
       THEN /\ lock' = [lock EXCEPT !.readers = @ + 1]
            /\ guards' = guards \cup {[t |-> "read"]}
            /\ activeThreads' = activeThreads \cup {t}
            /\ queue' = queue
       ELSE /\ queue' = Append(queue, <<[t |-> "read"]>>)
            /\ UNCHANGED <<lock, guards, activeThreads>>

AcquireWrite(t) == 
    /\ t \notin activeThreads
    /\ IF CanAcquireWrite 
       THEN /\ lock' = [lock EXCEPT !.writer = TRUE]
            /\ guards' = guards \cup {[t |-> "write"]}
            /\ activeThreads' = activeThreads \cup {t}
            /\ queue' = queue
       ELSE /\ queue' = Append(queue, <<[t |-> "write"]>>)
            /\ UNCHANGED <<lock, guards, activeThreads>>

AcquireUpread(t) == 
    /\ t \notin activeThreads
    /\ IF CanAcquireUpread 
       THEN /\ lock' = [lock EXCEPT !.upreader = TRUE]
            /\ guards' = guards \cup {[t |-> "upread"]}
            /\ activeThreads' = activeThreads \cup {t}
            /\ queue' = queue
       ELSE /\ queue' = Append(queue, <<[t |-> "upread"]>>)
            /\ UNCHANGED <<lock, guards, activeThreads>>

(* Release operations *)
ReleaseRead(t) == 
    /\ [t |-> "read"] \in guards
    /\ lock' = [lock EXCEPT !.readers = @ - 1]
    /\ guards' = guards \ {[t |-> "read"]}
    /\ activeThreads' = activeThreads \ {t}
    /\ \E head \in DOMAIN queue: 
        LET op == queue[head] IN
        IF op.type = "read" \/ (op.type = "upread" /\ CanAcquireUpread) \/ (op.type = "write" /\ CanAcquireWrite)
        THEN queue' = [i \in 1..(Len(queue)-1) |-> IF i < head THEN queue[i] ELSE queue[i+1]]
        ELSE queue' = queue

ReleaseWrite(t) == 
    /\ [t |-> "write"] \in guards
    /\ lock' = [lock EXCEPT !.writer = FALSE]
    /\ guards' = guards \ {[t |-> "write"]}
    /\ activeThreads' = activeThreads \ {t}
    /\ \A i \in DOMAIN queue: 
        LET op == queue[i] IN
        IF op.type = "read" /\ CanAcquireRead \/ op.type = "upread" /\ CanAcquireUpread \/ op.type = "write" /\ CanAcquireWrite
        THEN queue' = <<>>
        ELSE queue' = queue

ReleaseUpread(t) == 
    /\ [t |-> "upread"] \in guards
    /\ lock' = [lock EXCEPT !.upreader = FALSE, !.upgrading = FALSE]
    /\ guards' = guards \ {[t |-> "upread"]}
    /\ activeThreads' = activeThreads \ {t}
    /\ \A i \in DOMAIN queue: 
        LET op == queue[i] IN
        IF op.type = "read" /\ CanAcquireRead \/ op.type = "upread" /\ CanAcquireUpread \/ op.type = "write" /\ CanAcquireWrite
        THEN queue' = <<>>
        ELSE queue' = queue

(* Upgrade operation *)
Upgrade(t) == 
    /\ [t |-> "upread"] \in guards
    /\ lock.upreader = TRUE
    /\ lock' = IF CanUpgrade 
               THEN [lock EXCEPT !.writer = TRUE, !.upreader = FALSE, !.upgrading = FALSE]
               ELSE [lock EXCEPT !.upgrading = TRUE]
    /\ IF CanUpgrade 
       THEN /\ guards' = (guards \ {[t |-> "upread"]}) \cup {[t |-> "write"]}
            /\ queue' = queue
       ELSE /\ guards' = guards
            /\ queue' = queue
    /\ activeThreads' = activeThreads

(* Downgrade operation *)
Downgrade(t) == 
    /\ [t |-> "write"] \in guards
    /\ lock' = [lock EXCEPT !.writer = FALSE, !.upreader = TRUE]
    /\ guards' = (guards \ {[t |-> "write"]}) \cup {[t |-> "upread"]}
    /\ activeThreads' = activeThreads
    /\ queue' = queue

(* Next state relation *)
Next == 
    \/ \E t \in Threads: AcquireRead(t)
    \/ \E t \in Threads: AcquireWrite(t)
    \/ \E t \in Threads: AcquireUpread(t)
    \/ \E t \in Threads: ReleaseRead(t)
    \/ \E t \in Threads: ReleaseWrite(t)
    \/ \E t \in Threads: ReleaseUpread(t)
    \/ \E t \in Threads: Upgrade(t)
    \/ \E t \in Threads: Downgrade(t)

(* Specification with fairness *)
Spec == 
    Init 
    /\ [][Next]_<<lock, queue, guards, activeThreads>>
    /\ WF_<<lock, queue, guards, activeThreads>>(Next)

====