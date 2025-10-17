---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads, Data

VARIABLES lock_state, wait_queue, readers, writers, upreaders, upgrading

(* Bit field constants matching the Rust implementation *)
WRITER == 1 << (63)
UPGRADEABLE_READER == 1 << (62)
BEING_UPGRADED == 1 << (61)
READER_INCREMENT == 1

(* State predicates *)
IsFree(state) == state = 0
HasWriter(state) == state /\ WRITER /= 0
HasUpreader(state) == state /\ UPGRADEABLE_READER /= 0
IsUpgrading(state) == state /\ BEING_UPGRADED /= 0
ReaderCount(state) == state % (1 << 61)

(* Acquisition conditions *)
CanAcquireRead(state) == ~HasWriter(state) /\ ~IsUpgrading(state)
CanAcquireWrite(state) == IsFree(state)
CanAcquireUpread(state) == ~HasWriter(state) /\ ~HasUpreader(state)
CanUpgrade(state) == HasUpreader(state) /\ IsUpgrading(state) /\ ReaderCount(state) = 0

(* State modification operations *)
AcquireRead(state) == state + READER_INCREMENT
AcquireWrite(state) == state + WRITER
AcquireUpread(state) == state + UPGRADEABLE_READER
StartUpgrade(state) == state + BEING_UPGRADED
CompleteUpgrade(state) == (state - UPGRADEABLE_READER - BEING_UPGRADED) + WRITER
ReleaseRead(state) == state - READER_INCREMENT
ReleaseWrite(state) == state - WRITER
ReleaseUpread(state) == state - UPGRADEABLE_READER
Downgrade(state) == (state - WRITER) + UPGRADEABLE_READER

(* Type invariant *)
TypeOK == 
    /\ lock_state \in Nat
    /\ wait_queue \in Seq(Threads)
    /\ readers \in [Threads -> Nat]
    /\ writers \in [Threads -> BOOLEAN]
    /\ upreaders \in [Threads -> BOOLEAN]
    /\ upgrading \in [Threads -> BOOLEAN]
    /\ \A t \in Threads: 
        /\ readers[t] \in Nat 
        /\ ~(writers[t] /\ upreaders[t])
        /\ ~(writers[t] /\ upgrading[t])
        /\ (upgrading[t] => upreaders[t])

(* Initial state *)
Init == 
    /\ lock_state = 0
    /\ wait_queue = <<>>
    /\ readers = [t \in Threads |-> 0]
    /\ writers = [t \in Threads |-> FALSE]
    /\ upreaders = [t \in Threads |-> FALSE]
    /\ upgrading = [t \in Threads |-> FALSE]

(* Reader acquisition *)
AcquireRead(t) == 
    /\ ~readers[t] > 0 /\ ~writers[t] /\ ~upreaders[t] /\ ~upgrading[t]
    /\ LET new_state = AcquireRead(lock_state) IN
        IF CanAcquireRead(lock_state) THEN
            /\ lock_state' = new_state
            /\ readers' = [readers EXCEPT ![t] = @ + 1]
            /\ UNCHANGED <<wait_queue, writers, upreaders, upgrading>>
        ELSE
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED <<lock_state, readers, writers, upreaders, upgrading>>

(* Writer acquisition *)
AcquireWrite(t) == 
    /\ ~readers[t] > 0 /\ ~writers[t] /\ ~upreaders[t] /\ ~upgrading[t]
    /\ LET new_state = AcquireWrite(lock_state) IN
        IF CanAcquireWrite(lock_state) THEN
            /\ lock_state' = new_state
            /\ writers' = [writers EXCEPT ![t] = TRUE]
            /\ UNCHANGED <<wait_queue, readers, upreaders, upgrading>>
        ELSE
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED <<lock_state, readers, writers, upreaders, upgrading>>

(* Upgradeable reader acquisition *)
AcquireUpread(t) == 
    /\ ~readers[t] > 0 /\ ~writers[t] /\ ~upreaders[t] /\ ~upgrading[t]
    /\ LET new_state = AcquireUpread(lock_state) IN
        IF CanAcquireUpread(lock_state) THEN
            /\ lock_state' = new_state
            /\ upreaders' = [upreaders EXCEPT ![t] = TRUE]
            /\ UNCHANGED <<wait_queue, readers, writers, upgrading>>
        ELSE
            /\ wait_queue' = Append(wait_queue, t)
            /\ UNCHANGED <<lock_state, readers, writers, upreaders, upgrading>>

(* Reader release *)
ReleaseRead(t) == 
    /\ readers[t] > 0
    /\ lock_state' = ReleaseRead(lock_state)
    /\ readers' = [readers EXCEPT ![t] = @ - 1]
    /\ IF ReaderCount(lock_state') = 0 THEN
            /\ wait_queue' = IF wait_queue /= <<>> THEN Tail(wait_queue) ELSE <<>>
            /\ UNCHANGED <<writers, upreaders, upgrading>>
        ELSE
            /\ UNCHANGED <<wait_queue, writers, upreaders, upgrading>>

(* Writer release *)
ReleaseWrite(t) == 
    /\ writers[t]
    /\ lock_state' = ReleaseWrite(lock_state)
    /\ writers' = [writers EXCEPT ![t] = FALSE]
    /\ wait_queue' = <<>>  (* wake_all semantics *)
    /\ UNCHANGED <<readers, upreaders, upgrading>>

(* Upgradeable reader release *)
ReleaseUpread(t) == 
    /\ upreaders[t] /\ ~upgrading[t]
    /\ lock_state' = ReleaseUpread(lock_state)
    /\ upreaders' = [upreaders EXCEPT ![t] = FALSE]
    /\ wait_queue' = <<>>  (* wake_all semantics *)
    /\ UNCHANGED <<readers, writers, upgrading>>

(* Start upgrade process *)
StartUpgrade(t) == 
    /\ upreaders[t] /\ ~upgrading[t]
    /\ lock_state' = StartUpgrade(lock_state)
    /\ upgrading' = [upgrading EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<wait_queue, readers, writers, upreaders>>

(* Complete upgrade *)
CompleteUpgrade(t) == 
    /\ upreaders[t] /\ upgrading[t]
    /\ LET new_state = CompleteUpgrade(lock_state) IN
        IF CanUpgrade(lock_state) THEN
            /\ lock_state' = new_state
            /\ upreaders' = [upreaders EXCEPT ![t] = FALSE]
            /\ writers' = [writers EXCEPT ![t] = TRUE]
            /\ upgrading' = [upgrading EXCEPT ![t] = FALSE]
            /\ UNCHANGED <<wait_queue, readers>>
        ELSE
            /\ UNCHANGED <<lock_state, wait_queue, readers, writers, upreaders, upgrading>>

(* Downgrade from writer to upgradeable reader *)
Downgrade(t) == 
    /\ writers[t]
    /\ lock_state' = Downgrade(lock_state)
    /\ writers' = [writers EXCEPT ![t] = FALSE]
    /\ upreaders' = [upreaders EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<wait_queue, readers, upgrading>>

(* Next-state relation *)
Next == 
    \/ \E t \in Threads: AcquireRead(t)
    \/ \E t \in Threads: AcquireWrite(t)
    \/ \E t \in Threads: AcquireUpread(t)
    \/ \E t \in Threads: ReleaseRead(t)
    \/ \E t \in Threads: ReleaseWrite(t)
    \/ \E t \in Threads: ReleaseUpread(t)
    \/ \E t \in Threads: StartUpgrade(t)
    \/ \E t \in Threads: CompleteUpgrade(t)
    \/ \E t \in Threads: Downgrade(t)

(* Fairness assumptions *)
Spec == 
    /\ Init
    /\ [][Next]_<<lock_state, wait_queue, readers, writers, upreaders, upgrading>>
    /\ WF_<<lock_state, wait_queue, readers, writers, upreaders, upgrading>>(Next)

====