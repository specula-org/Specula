
---- MODULE mutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads
VARIABLES holder, wait_queue, awakened

TypeOK == 
    holder \subseteq Threads /\ Cardinality(holder) <= 1
    /\ wait_queue \in Seq(Threads)
    /\ awakened \subseteq Threads

Init == 
    holder = {} 
    /\ wait_queue = << >> 
    /\ awakened = {}

Lock(t) == 
    /\ t \in Threads
    /\ t \notin holder
    /\ t \notin wait_queue
    /\ t \notin awakened
    /\ IF holder = {}
       THEN 
           holder' = {t}
           /\ UNCHANGED <<wait_queue, awakened>>
       ELSE
           wait_queue' = Append(wait_queue, t)
           /\ UNCHANGED <<holder, awakened>>

TryLock(t) == 
    /\ t \in Threads
    /\ t \notin holder
    /\ t \notin wait_queue
    /\ IF holder = {}
       THEN 
           holder' = {t}
           /\ awakened' = awakened \ {t}
           /\ UNCHANGED wait_queue
       ELSE
           /\ IF t \in awakened
              THEN 
                  wait_queue' = Append(wait_queue, t)
                  /\ awakened' = awakened \ {t}
              ELSE 
                  /\ UNCHANGED <<wait_queue, awakened>>
           /\ UNCHANGED holder

Unlock(t) == 
    /\ t \in holder
    /\ holder' = {}
    /\ IF wait_queue = << >>
       THEN 
           /\ UNCHANGED <<wait_queue, awakened>>
       ELSE
           /\ wait_queue' = Tail(wait_queue)
           /\ awakened' = awakened \union {Head(wait_queue)}

Next(t) == Lock(t) \/ TryLock(t) \/ Unlock(t)
Next == \E t \in Threads: Next(t)
Vars == <<holder, wait_queue, awakened>>
Spec == Init /\ [][Next]_Vars /\ \A t \in Threads : WF_Vars(Next(t))
====