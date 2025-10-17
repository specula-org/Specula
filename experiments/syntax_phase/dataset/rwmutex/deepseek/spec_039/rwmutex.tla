---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS THREADS, MaxReaders

VARIABLES lock_state, queue, guards, active_operations

(* Constants for bit positions *)
WRITER == 1
UPGRADEABLE_READER == 2
BEING_UPGRADED == 4
MAX_READER == MaxReaders
READER == 8

(* State representation *)
ReaderCount(state) == state \div READER
WriterBit(state) == IF state \mod (WRITER * 2) >= WRITER THEN TRUE ELSE FALSE
UpgradeableReaderBit(state) == IF state \mod (UPGRADEABLE_READER * 2) >= UPGRADEABLE_READER THEN TRUE ELSE FALSE
BeingUpgradedBit(state) == IF state \mod (BEING_UPGRADED * 2) >= BEING_UPGRADED THEN TRUE ELSE FALSE

(* Type invariant *)
TypeOK == 
    /\ lock_state \in 0..(WRITER + UPGRADEABLE_READER + BEING_UPGRADED + (MAX_READER * READER - 1))
    /\ queue \in Seq(THREADS)
    /\ guards \in [THREADS -> { "None", "Read", "Write", "UpRead" }]
    /\ active_operations \in SUBSET THREADS
    /\ \A t \in THREADS: 
        IF guards[t] = "Read" THEN ReaderCount(lock_state) > 0
        ELSE IF guards[t] = "Write" THEN WriterBit(lock_state)
        ELSE IF guards[t] = "UpRead" THEN UpgradeableReaderBit(lock_state)
        ELSE TRUE

(* Initial state *)
Init == 
    /\ lock_state = 0
    /\ queue = <<>>
    /\ guards = [t \in THREADS |-> "None"]
    /\ active_operations = {}

(* Try to acquire read lock - matches Rust try_read logic *)
TryRead(t) ==
    /\ guards[t] = "None"
    /\ t \notin active_operations
    /\ LET new_state == lock_state + READER IN
        IF new_state \div READER < MAX_READER /\ ~WriterBit(new_state) /\ ~BeingUpgradedBit(new_state) THEN
            /\ lock_state' = new_state
            /\ guards' = [guards EXCEPT ![t] = "Read"]
            /\ active_operations' = active_operations \cup {t}
            /\ UNCHANGED queue
        ELSE
            /\ lock_state' = lock_state
            /\ UNCHANGED <<guards, queue, active_operations>>

(* Try to acquire write lock - matches Rust try_write logic *)
TryWrite(t) ==
    /\ guards[t] = "None" 
    /\ t \notin active_operations
    /\ lock_state = 0
    /\ lock_state' = WRITER
    /\ guards' = [guards EXCEPT ![t] = "Write"]
    /\ active_operations' = active_operations \cup {t}
    /\ UNCHANGED queue

(* Try to acquire upgradeable read lock - matches Rust try_upread logic *)
TryUpRead(t) ==
    /\ guards[t] = "None"
    /\ t \notin active_operations
    /\ LET current_bits == lock_state \cap (WRITER + UPGRADEABLE_READER) IN
        IF current_bits = 0 THEN
            /\ lock_state' = lock_state + UPGRADEABLE_READER
            /\ guards' = [guards EXCEPT ![t] = "UpRead"]
            /\ active_operations' = active_operations \cup {t}
            /\ UNCHANGED queue
        ELSE IF current_bits = WRITER THEN
            /\ FALSE
        ELSE
            /\ FALSE

(* Release read lock - matches Rust drop logic *)
ReleaseRead(t) ==
    /\ guards[t] = "Read"
    /\ t \in active_operations
    /\ LET new_state == lock_state - READER IN
        /\ lock_state' = new_state
        /\ guards' = [guards EXCEPT ![t] = "None"]
        /\ active_operations' = active_operations \ {t}
        /\ IF new_state \div READER = 0 /\ new_state \mod READER = 0 THEN
            /\ IF queue /= <<>> THEN
                queue' = Tail(queue)
               ELSE
                queue' = queue
           ELSE
            /\ UNCHANGED queue

(* Release write lock - matches Rust drop logic *)
ReleaseWrite(t) ==
    /\ guards[t] = "Write"
    /\ t \in active_operations
    /\ lock_state' = 0
    /\ guards' = [guards EXCEPT ![t] = "None"]
    /\ active_operations' = active_operations \ {t}
    /\ queue' = <<>>

(* Release upgradeable read lock - matches Rust drop logic *)
ReleaseUpRead(t) ==
    /\ guards[t] = "UpRead"
    /\ t \in active_operations
    /\ LET new_state == lock_state - UPGRADEABLE_READER IN
        /\ lock_state' = new_state
        /\ guards' = [guards EXCEPT ![t] = "None"]
        /\ active_operations' = active_operations \ {t}
        /\ IF new_state = 0 THEN
            /\ queue' = <<>>
        ELSE
            /\ UNCHANGED queue

(* Upgrade from upread to write - matches Rust upgrade logic *)
Upgrade(t) ==
    /\ guards[t] = "UpRead"
    /\ t \in active_operations
    /\ LET target_state == UPGRADEABLE_READER + BEING_UPGRADED IN
        IF lock_state = target_state THEN
            /\ lock_state' = WRITER
            /\ guards' = [guards EXCEPT ![t] = "Write"]
            /\ UNCHANGED <<queue, active_operations>>
        ELSE
            /\ lock_state' = lock_state + BEING_UPGRADED
            /\ UNCHANGED <<guards, queue, active_operations>>

(* Downgrade from write to upread - matches Rust downgrade logic *)
Downgrade(t) ==
    /\ guards[t] = "Write" 
    /\ t \in active_operations
    /\ lock_state = WRITER
    /\ lock_state' = UPGRADEABLE_READER
    /\ guards' = [guards EXCEPT ![t] = "UpRead"]
    /\ UNCHANGED <<queue, active_operations>>

(* Enqueue operations with blocking semantics *)
EnqueueRead(t) ==
    /\ guards[t] = "None"
    /\ t \notin active_operations
    /\ queue' = Append(queue, t)
    /\ guards' = [guards EXCEPT ![t] = "Read"]
    /\ UNCHANGED <<lock_state, active_operations>>

EnqueueWrite(t) ==
    /\ guards[t] = "None"
    /\ t \notin active_operations  
    /\ queue' = Append(queue, t)
    /\ guards' = [guards EXCEPT ![t] = "Write"]
    /\ UNCHANGED <<lock_state, active_operations>>

EnqueueUpRead(t) ==
    /\ guards[t] = "None"
    /\ t \notin active_operations
    /\ queue' = Append(queue, t)
    /\ guards' = [guards EXCEPT ![t] = "UpRead"]
    /\ UNCHANGED <<lock_state, active_operations>>

(* Process queue head based on operation type *)
ProcessQueue ==
    /\ queue /= <<>>
    /\ LET head == Head(queue) IN
        \/ /\ TryRead(head)
           /\ queue' = Tail(queue)
        \/ /\ TryWrite(head) 
           /\ queue' = Tail(queue)
        \/ /\ TryUpRead(head)
           /\ queue' = Tail(queue)
        \/ /\ UNCHANGED <<lock_state, guards, queue, active_operations>>

(* Next state relation *)
Next ==
    \/ \E t \in THREADS: TryRead(t)
    \/ \E t \in THREADS: TryWrite(t)
    \/ \E t \in THREADS: TryUpRead(t)
    \/ \E t \in THREADS: ReleaseRead(t)
    \/ \E t \in THREADS: ReleaseWrite(t)
    \/ \E t \in THREADS: ReleaseUpRead(t)
    \/ \E t \in THREADS: Upgrade(t)
    \/ \E t \in THREADS: Downgrade(t)
    \/ \E t \in THREADS: EnqueueRead(t)
    \/ \E t \in THREADS: EnqueueWrite(t)
    \/ \E t \in THREADS: EnqueueUpRead(t)
    \/ ProcessQueue

(* Fairness specification *)
Spec == 
    /\ Init
    /\ [][Next]_<<lock_state, queue, guards, active_operations>>
    /\ WF_<<lock_state, queue, guards, active_operations>>(Next)

Vars == <<lock_state, queue, guards, active_operations>>
====