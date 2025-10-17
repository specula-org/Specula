
---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Threads

VARIABLES lock, queue, holders

(* State representation *)
State == [writer: BOOLEAN, upreader: BOOLEAN, upgrading: BOOLEAN, readers: Nat]

CanRead == lock.writer = FALSE /\ lock.upgrading = FALSE
CanWrite == lock.writer = FALSE /\ lock.upreader = FALSE /\ lock.readers = 0
CanUpRead == lock.writer = FALSE /\ lock.upreader = FALSE

Init == 
    lock = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0] /\
    queue = << >> /\
    holders = EmptyBag

ReadAcquire(t) ==
    IF CanRead
    THEN
        lock' = [lock EXCEPT !.readers = lock.readers + 1] /\
        holders' = BagAdd(holders, [thread |-> t, type |-> "Read"]) /\
        UNCHANGED <<queue>>
    ELSE
        queue' = Append(queue, [thread |-> t, op |-> "Read"]) /\
        UNCHANGED <<lock, holders>>
    
WriteAcquire(t) ==
    IF CanWrite
    THEN
        lock' = [lock EXCEPT !.writer = TRUE] /\
        holders' = BagAdd(holders, [thread |-> t, type |-> "Write"]) /\
        UNCHANGED <<queue>>
    ELSE
        queue' = Append(queue, [thread |-> t, op |-> "Write"]) /\
        UNCHANGED <<lock, holders>>
    
UpReadAcquire(t) ==
    IF CanUpRead
    THEN
        lock' = [lock EXCEPT !.upreader = TRUE] /\
        holders' = BagAdd(holders, [thread |-> t, type |-> "UpRead"]) /\
        UNCHANGED <<queue>>
    ELSE
        queue' = Append(queue, [thread |-> t, op |-> "UpRead"]) /\
        UNCHANGED <<lock, holders>>
    
ReadRelease(t) ==
    LET holder == [thread |-> t, type |-> "Read"]
    IN
    /\ holder \in holders
    /\ lock' = [lock EXCEPT !.readers = lock.readers - 1]
    /\ holders' = BagRemove(holders, holder)
    /\ IF lock = [writer |-> FALSE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 1]
       THEN /\ IF queue /= <<>>
               THEN queue' = Tail(queue)
               ELSE queue' = queue
       ELSE queue' = queue
    
WriteRelease(t) ==
    LET holder == [thread |-> t, type |-> "Write"]
    IN
    /\ holder \in holders
    /\ lock' = [lock EXCEPT !.writer = FALSE]
    /\ holders' = BagRemove(holders, holder)
    /\ queue' = << >>
    
UpReadRelease(t) ==
    LET holder == [thread |-> t, type |-> "UpRead"]
    IN
    /\ holder \in holders
    /\ lock' = [lock EXCEPT !.upreader = FALSE]
    /\ holders' = BagRemove(holders, holder)
    /\ IF lock = [writer |-> FALSE, upreader |-> TRUE, upgrading |-> FALSE, readers |-> 0]
       THEN queue' = << >>
       ELSE queue' = queue
    
StartUpgrade(t) ==
    LET holder == [thread |-> t, type |-> "UpRead"]
    IN
    /\ holder \in holders
    /\ lock.upgrading = FALSE
    /\ lock' = [lock EXCEPT !.upgrading = TRUE]
    /\ UNCHANGED <<queue, holders>>
    
FinishUpgrade(t) ==
    LET old_holder == [thread |-> t, type |-> "UpRead"]
        new_holder == [thread |-> t, type |-> "Write"]
    IN
    /\ old_holder \in holders
    /\ lock = [writer |-> FALSE, upreader |-> TRUE, upgrading |-> TRUE, readers |-> 0]
    /\ lock' = [writer |-> TRUE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ holders' = BagAdd(BagRemove(holders, old_holder), new_holder)
    /\ UNCHANGED <<queue>>
    
Downgrade(t) ==
    LET old_holder == [thread |-> t, type |-> "Write"]
        new_holder == [thread |-> t, type |-> "UpRead"]
    IN
    /\ old_holder \in holders
    /\ lock = [writer |-> TRUE, upreader |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ lock' = [writer |-> FALSE, upreader |-> TRUE, upgrading |-> FALSE, readers |-> 0]
    /\ holders' = BagAdd(BagRemove(holders, old_holder), new_holder)
    /\ UNCHANGED <<queue>>
    
Next == 
    \E t \in Threads:
        ReadAcquire(t) \/ WriteAcquire(t) \/ UpReadAcquire(t)
        \/ ReadRelease(t) \/ WriteRelease(t) \/ UpReadRelease(t)
        \/ StartUpgrade(t) \/ FinishUpgrade(t) \/ Downgrade(t)

Vars == <<lock, queue, holders>>
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====