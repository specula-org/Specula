---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, NULL

VARIABLES lock_state, wait_queue, active_ops

vars == <<lock_state, wait_queue, active_ops>>

Init == 
    /\ lock_state = [writer_bit |-> 0, upreader_bit |-> 0, being_upgraded |-> 0, reader_count |-> 0]
    /\ wait_queue = <<>>
    /\ active_ops = [x \in {} |-> ""]

\* Bit field helper operators
HasWriter == lock_state["writer_bit"] = 1
HasUpreader == lock_state["upreader_bit"] = 1
BeingUpgraded == lock_state["being_upgraded"] = 1
ReaderCount == lock_state["reader_count"]
CanAcquireReader == ~HasWriter /\ ~BeingUpgraded
CanAcquireWriter == lock_state = [writer_bit |-> 0, upreader_bit |-> 0, being_upgraded |-> 0, reader_count |-> 0]
CanAcquireUpread == ~HasWriter /\ ~HasUpreader

\* Core acquisition actions
AcquireRead(t) ==
    /\ t \notin DOMAIN active_ops
    /\ CanAcquireReader
    /\ lock_state' = [lock_state EXCEPT !["reader_count"] = lock_state["reader_count"] + 1]
    /\ active_ops' = active_ops @@ [t |-> "read"]
    /\ wait_queue' = wait_queue

AcquireWrite(t) ==
    /\ t \notin DOMAIN active_ops
    /\ CanAcquireWriter
    /\ lock_state' = [lock_state EXCEPT !["writer_bit"] = 1]
    /\ active_ops' = active_ops @@ [t |-> "write"]
    /\ wait_queue' = wait_queue

AcquireUpread(t) ==
    /\ t \notin DOMAIN active_ops
    /\ CanAcquireUpread
    /\ lock_state' = [lock_state EXCEPT !["upreader_bit"] = 1]
    /\ active_ops' = active_ops @@ [t |-> "upread"]
    /\ wait_queue' = wait_queue

\* Upgrade/downgrade transitions
UpgradeToWrite(t) ==
    /\ active_ops[t] = "upread"
    /\ ~BeingUpgraded
    /\ lock_state' = [lock_state EXCEPT !["being_upgraded"] = 1]
    /\ UNCHANGED <<active_ops, wait_queue>>

CompleteUpgrade(t) ==
    /\ active_ops[t] = "upread"
    /\ BeingUpgraded
    /\ ReaderCount = 0
    /\ lock_state' = [lock_state EXCEPT !["writer_bit"] = 1, !["being_upgraded"] = 0]
    /\ active_ops' = [active_ops EXCEPT ![t] = "write"]
    /\ wait_queue' = wait_queue

DowngradeToUpread(t) ==
    /\ active_ops[t] = "write"
    /\ lock_state' = [lock_state EXCEPT !["writer_bit"] = 0, !["upreader_bit"] = 1]
    /\ active_ops' = [active_ops EXCEPT ![t] = "upread"]
    /\ wait_queue' = wait_queue

\* Release operations with mixed wake strategies
ReleaseRead(t) ==
    /\ active_ops[t] = "read"
    /\ lock_state' = [lock_state EXCEPT !["reader_count"] = lock_state["reader_count"] - 1]
    /\ active_ops' = active_ops \ {t}
    /\ \/ /\ ReaderCount = 1  \* Last reader - wake_one
         /\ \E w \in Threads: w \notin DOMAIN active_ops
         /\ wait_queue' = Tail(wait_queue)
       \/ /\ ReaderCount > 1  \* Not last reader - no wake
         /\ wait_queue' = wait_queue

ReleaseWrite(t) ==
    /\ active_ops[t] = "write"
    /\ lock_state' = [lock_state EXCEPT !["writer_bit"] = 0]
    /\ active_ops' = active_ops \ {t}
    /\ wait_queue' = <<>>  \* wake_all

ReleaseUpread(t) ==
    /\ active_ops[t] = "upread"
    /\ lock_state' = [lock_state EXCEPT !["upreader_bit"] = 0]
    /\ active_ops' = active_ops \ {t}
    /\ wait_queue' = <<>>  \* wake_all

\* Wait queue management
EnqueueRead(t) ==
    /\ t \notin DOMAIN active_ops
    /\ ~CanAcquireReader
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED <<lock_state, active_ops>>

EnqueueWrite(t) ==
    /\ t \notin DOMAIN active_ops
    /\ ~CanAcquireWriter
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED <<lock_state, active_ops>>

EnqueueUpread(t) ==
    /\ t \notin DOMAIN active_ops
    /\ ~CanAcquireUpread
    /\ wait_queue' = Append(wait_queue, t)
    /\ UNCHANGED <<lock_state, active_ops>>

Next == 
    \/ \E t \in Threads: AcquireRead(t)
    \/ \E t \in Threads: AcquireWrite(t)
    \/ \E t \in Threads: AcquireUpread(t)
    \/ \E t \in Threads: UpgradeToWrite(t)
    \/ \E t \in Threads: CompleteUpgrade(t)
    \/ \E t \in Threads: DowngradeToUpread(t)
    \/ \E t \in Threads: ReleaseRead(t)
    \/ \E t \in Threads: ReleaseWrite(t)
    \/ \E t \in Threads: ReleaseUpread(t)
    \/ \E t \in Threads: EnqueueRead(t)
    \/ \E t \in Threads: EnqueueWrite(t)
    \/ \E t \in Threads: EnqueueUpread(t)

Spec == Init /\ [][Next]_vars /\ \A t \in Threads: WF_vars(ReleaseRead(t)) /\ \A u \in Threads: WF_vars(ReleaseWrite(u)) /\ \A v \in Threads: WF_vars(ReleaseUpread(v))
====