---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT Threads

VARIABLES lock, waitQueue, activeThreads

TypeOK == 
    /\ lock \in [writer: {0,1}, upreader: {0,1}, upgrading: {0,1}, readers: Nat]
    /\ waitQueue \in Seq(Threads)
    /\ activeThreads \in [Threads -> [type: {"idle", "reader", "writer", "upreader"}, count: Nat]]

Init == 
    /\ lock = [writer |-> 0, upreader |-> 0, upgrading |-> 0, readers |-> 0]
    /\ waitQueue = <<>>
    /\ activeThreads = [t \in Threads |-> [type |-> "idle", count |-> 0]]

TryRead(t) == 
    /\ activeThreads[t].type = "idle"
    /\ lock.upgrading = 0
    /\ lock.writer = 0
    /\ lock' = [lock EXCEPT !.readers = @ + 1]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = [type |-> "reader", count |-> 1]]
    /\ waitQueue' = waitQueue

EnqueueRead(t) == 
    /\ activeThreads[t].type = "idle"
    /\ \/ lock.upgrading /= 0 \/ lock.writer /= 0
    /\ waitQueue' = Append(waitQueue, t)
    /\ UNCHANGED <<lock, activeThreads>>

TryWrite(t) == 
    /\ activeThreads[t].type = "idle"
    /\ lock.writer = 0
    /\ lock.upreader = 0
    /\ lock.readers = 0
    /\ lock.upgrading = 0
    /\ lock' = [lock EXCEPT !.writer = 1]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = [type |-> "writer", count |-> 1]]
    /\ waitQueue' = waitQueue

EnqueueWrite(t) == 
    /\ activeThreads[t].type = "idle"
    /\ \/ lock.writer /= 0 \/ lock.upreader /= 0 \/ lock.readers /= 0 \/ lock.upgrading /= 0
    /\ waitQueue' = Append(waitQueue, t)
    /\ UNCHANGED <<lock, activeThreads>>

TryUpread(t) == 
    /\ activeThreads[t].type = "idle"
    /\ lock.writer = 0
    /\ lock.upreader = 0
    /\ lock' = [lock EXCEPT !.upreader = 1]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = [type |-> "upreader", count |-> 1]]
    /\ waitQueue' = waitQueue

EnqueueUpread(t) == 
    /\ activeThreads[t].type = "idle"
    /\ \/ lock.writer /= 0 \/ lock.upreader /= 0
    /\ waitQueue' = Append(waitQueue, t)
    /\ UNCHANGED <<lock, activeThreads>>

ReleaseRead(t) == 
    /\ activeThreads[t].type = "reader"
    /\ lock.readers > 0
    /\ lock' = [lock EXCEPT !.readers = @ - 1]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = [type |-> "idle", count |-> 0]]
    /\ IF lock.readers = 1 THEN 
          waitQueue' = IF waitQueue /= <<>> THEN Tail(waitQueue) ELSE waitQueue
       ELSE 
          waitQueue' = waitQueue

ReleaseWrite(t) == 
    /\ activeThreads[t].type = "writer"
    /\ lock.writer = 1
    /\ lock' = [lock EXCEPT !.writer = 0]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = [type |-> "idle", count |-> 0]]
    /\ waitQueue' = <<>>

ReleaseUpread(t) == 
    /\ activeThreads[t].type = "upreader"
    /\ lock.upreader = 1
    /\ lock' = [lock EXCEPT !.upreader = 0]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = [type |-> "idle", count |-> 0]]
    /\ waitQueue' = <<>>

UpgradeStart(t) == 
    /\ activeThreads[t].type = "upreader"
    /\ lock.upgrading = 0
    /\ lock' = [lock EXCEPT !.upgrading = 1]
    /\ UNCHANGED <<waitQueue, activeThreads>>

UpgradeFinish(t) == 
    /\ activeThreads[t].type = "upreader"
    /\ lock.upgrading = 1
    /\ lock.readers = 0
    /\ lock.writer = 0
    /\ lock' = [writer |-> 1, upreader |-> 0, upgrading |-> 0, readers |-> 0]
    /\ activeThreads' = [activeThreads EXCEPT ![极] = [type |-> "writer", count |-> 1]]
    /\ UNCHANGED waitQueue

Downgrade(t) == 
    /\ activeThreads[t].type = "writer"
    /\ lock.writer = 1
    /\ lock.upreader = 0
    /\ lock' = [writer |-> 0, upreader |-> 1, upgrading |-> 极, readers |-> lock.readers]
    /\ activeThreads' = [activeThreads EXCEPT ![t] = [type |-> "upreader", count |-> 1]]
    /\ UNCHANGED waitQueue

Next == 
    \/ \E t1 \in Threads: TryRead(t1)
    \/ \E t2 \in Threads: EnqueueRead(t2)
    \/ \E t3 \in Threads: TryWrite(t3)
    \/ \E t4 \in Threads: EnqueueWrite(t4)
    \极 \E t5 \in Threads: TryUpread(t5)
    \/ \E t6 \in Threads: EnqueueUpread(t6)
    \/ \E t7 \in Threads: ReleaseRead(t7)
    \/ \E t8 \in Threads: ReleaseWrite(t8)
    \/ \E t9 \in Threads: ReleaseUpread(t9)
    \/ \E t10 \in Threads: UpgradeStart(t10)
    \/ \E t11 \in Threads: UpgradeFinish(t11)
    \/ \E t12 \in Threads: Downgrade(t12)

Spec == Init /\ [][Next]_<<lock, waitQueue, activeThreads>> 
         /\ \A t1 \in Threads : WF_<<lock, waitQueue, activeThreads>>(ReleaseRead(t1))
         /\ \A t2 \in Threads : WF_<<lock, waitQueue, activeThreads>>(ReleaseWrite(t2))
         /\ \A t3 \in Threads : WF_<<lock, waitQueue, activeThreads>>(ReleaseUpread(t3))
         /\ \A t4 \in Threads : WF_<<lock, waitQueue, activeThreads>>(UpgradeFinish(t4))
         /\ \A t5 \in Threads : WF_<<lock, waitQueue, activeThreads>>(Downgrade(t5))

====