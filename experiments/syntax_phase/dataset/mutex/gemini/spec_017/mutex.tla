---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS Threads
ASSUME Threads = {"t1", "t2"}

Nil == "Nil"

ThreadStates == {"Idle", "Reading", "Writing", "UpReading", "Upgrading", "Waiting"}
OpType == {"Read", "Write", "UpRead"}

VARIABLES
    lock_state,
    holders,
    wait_queue,
    pc

vars == <<lock_state, holders, wait_queue, pc>>

TypeOK ==
    /\ lock_state \in [ writer: BOOLEAN, upread: BOOLEAN, upgrading: BOOLEAN, readers: Nat ]
    /\ holders \in [ readers: SUBSET Threads,
                     writer: Threads \union {Nil},
                     upreader: Threads \union {Nil},
                     upgrading: Threads \union {Nil} ]
    /\ wait_queue \in Seq([who: Threads, for: OpType])
    /\ pc \in [Threads -> ThreadStates]
    /\ lock_state["writer"] <=> (holders["writer"] /= Nil)
    /\ lock_state["upread"] <=> (holders["upreader"] /= Nil)
    /\ lock_state["upgrading"] <=> (holders["upgrading"] /= Nil)
    /\ lock_state["readers"] = Cardinality(holders["readers"])
    /\ \A t \in Threads: (pc[t] = "Waiting") <=> (\E i \in 1..Len(wait_queue): wait_queue[i]["who"] = t)

Init ==
    /\ lock_state = [writer |-> FALSE, upread |-> FALSE, upgrading |-> FALSE, readers |-> 0]
    /\ holders = [readers |-> {}, writer |-> Nil, upreader |-> Nil, upgrading |-> Nil]
    /\ wait_queue = <<>>
    /\ pc = [t \in Threads |-> "Idle"]

CanReadLock == lock_state["writer"] = FALSE /\ lock_state["upgrading"] = FALSE
CanWriteLock == lock_state["writer"] = FALSE /\ lock_state["upread"] = FALSE /\ lock_state["readers"] = 0
CanUpReadLock == lock_state["writer"] = FALSE /\ lock_state["upread"] = FALSE

ReadLock(t) ==
    /\ pc[t] = "Idle"
    /\ CanReadLock
    /\ pc' = [pc EXCEPT ![t] = "Reading"]
    /\ holders' = [holders EXCEPT !["readers"] = @ \union {t}]
    /\ lock_state' = [lock_state EXCEPT !["readers"] = @ + 1]
    /\ UNCHANGED <<wait_queue>>

ReadWait(t) ==
    /\ pc[t] = "Idle"
    /\ \lnot CanReadLock
    /\ pc' = [pc EXCEPT ![t] = "Waiting"]
    /\ wait_queue' = Append(wait_queue, [who |-> t, for |-> "Read"])
    /\ UNCHANGED <<lock_state, holders>>

WriteLock(t) ==
    /\ pc[t] = "Idle"
    /\ CanWriteLock
    /\ pc' = [pc EXCEPT ![t] = "Writing"]
    /\ holders' = [holders EXCEPT !["writer"] = t]
    /\ lock_state' = [lock_state EXCEPT !["writer"] = TRUE]
    /\ UNCHANGED <<wait_queue>>

WriteWait(t) ==
    /\ pc[t] = "Idle"
    /\ \lnot CanWriteLock
    /\ pc' = [pc EXCEPT ![t] = "Waiting"]
    /\ wait_queue' = Append(wait_queue, [who |-> t, for |-> "Write"])
    /\ UNCHANGED <<lock_state, holders>>

UpReadLock(t) ==
    /\ pc[t] = "Idle"
    /\ CanUpReadLock
    /\ pc' = [pc EXCEPT ![t] = "UpReading"]
    /\ holders' = [holders EXCEPT !["upreader"] = t]
    /\ lock_state' = [lock_state EXCEPT !["upread"] = TRUE]
    /\ UNCHANGED <<wait_queue>>

UpReadWait(t) ==
    /\ pc[t] = "Idle"
    /\ \lnot CanUpReadLock
    /\ pc' = [pc EXCEPT ![t] = "Waiting"]
    /\ wait_queue' = Append(wait_queue, [who |-> t, for |-> "UpRead"])
    /\ UNCHANGED <<lock_state, holders>>

Upgrade(t) ==
    /\ pc[t] = "UpReading"
    /\ pc' = [pc EXCEPT ![t] = "Upgrading"]
    /\ holders' = [holders EXCEPT !["upreader"] = Nil, !["upgrading"] = t]
    /\ lock_state' = [lock_state EXCEPT !["upread"] = FALSE, !["upgrading"] = TRUE]
    /\ UNCHANGED <<wait_queue>>

CompleteUpgrade(t) ==
    /\ pc[t] = "Upgrading"
    /\ lock_state["readers"] = 0
    /\ pc' = [pc EXCEPT ![t] = "Writing"]
    /\ holders' = [holders EXCEPT !["upgrading"] = Nil, !["writer"] = t]
    /\ lock_state' = [lock_state EXCEPT !["upgrading"] = FALSE, !["writer"] = TRUE]
    /\ UNCHANGED <<wait_queue>>

ReaderPrefixLen(q) ==
    CHOOSE n \in 0..Len(q) :
        (\A i \in 1..n : q[i]["for"] = "Read")
        /\ ( (n = Len(q)) \/ (q[n+1]["for"] /= "Read") )

WakeAllReaders(q, new_pc, new_holders, new_lock_state) ==
    LET
        prefix_len == ReaderPrefixLen(q)
        woken_set == {q[i]["who"] : i \in 1..prefix_len}
        woken_count == Cardinality(woken_set)
        
        final_pc == [p \in DOMAIN new_pc |-> IF p \in woken_set THEN "Reading" ELSE new_pc[p]]
        final_holders == [new_holders EXCEPT !["readers"] = @ \union woken_set]
        final_lock_state == [new_lock_state EXCEPT !["readers"] = @ + woken_count]
        final_wait_queue == SubSeq(q, prefix_len + 1, Len(q))
    IN
        <<final_pc, final_holders, final_lock_state, final_wait_queue>>

Downgrade(t) ==
    /\ pc[t] = "Writing"
    /\ LET
        new_pc == [pc EXCEPT ![t] = "UpReading"]
        new_holders == [holders EXCEPT !["writer"] = Nil, !["upreader"] = t]
        new_lock_state == [lock_state EXCEPT !["writer"] = FALSE, !["upread"] = TRUE]
        
        result == WakeAllReaders(wait_queue, new_pc, new_holders, new_lock_state)
       IN
        /\ pc' = result[1]
        /\ holders' = result[2]
        /\ lock_state' = result[3]
        /\ wait_queue' = result[4]

ReadUnlock(t) ==
    /\ pc[t] = "Reading"
    /\ LET
        new_pc == [pc EXCEPT ![t] = "Idle"]
        new_holders == [holders EXCEPT !["readers"] = @ \ {t}]
        new_lock_state == [lock_state EXCEPT !["readers"] = @ - 1]
        
        WakeCondition == new_lock_state["readers"] = 0 /\ Len(wait_queue) > 0
       IN
        IF WakeCondition THEN
            LET Waiter == Head(wait_queue) IN
            IF Waiter["for"] = "Write" /\ new_lock_state["upread"] = FALSE THEN
                /\ pc' = [new_pc EXCEPT ![Waiter["who"]] = "Writing"]
                /\ holders' = [new_holders EXCEPT !["writer"] = Waiter["who"]]
                /\ lock_state' = [new_lock_state EXCEPT !["writer"] = TRUE]
                /\ wait_queue' = Tail(wait_queue)
            ELSE IF Waiter["for"] = "UpRead" /\ new_lock_state["writer"] = FALSE /\ new_lock_state["upread"] = FALSE THEN
                /\ pc' = [new_pc EXCEPT ![Waiter["who"]] = "UpReading"]
                /\ holders' = [new_holders EXCEPT !["upreader"] = Waiter["who"]]
                /\ lock_state' = [new_lock_state EXCEPT !["upread"] = TRUE]
                /\ wait_queue' = Tail(wait_queue)
            ELSE
                /\ pc' = new_pc
                /\ holders' = new_holders
                /\ lock_state' = new_lock_state
                /\ wait_queue' = wait_queue
        ELSE
            /\ pc' = new_pc
            /\ holders' = new_holders
            /\ lock_state' = new_lock_state
            /\ wait_queue' = wait_queue

WriteUnlock(t) ==
    /\ pc[t] = "Writing"
    /\ LET
        new_pc == [pc EXCEPT ![t] = "Idle"]
        new_holders == [holders EXCEPT !["writer"] = Nil]
        new_lock_state == [lock_state EXCEPT !["writer"] = FALSE]
        
        WakeCondition == Len(wait_queue) > 0
       IN
        IF WakeCondition THEN
            LET Waiter == Head(wait_queue) IN
            IF Waiter["for"] = "Write" THEN
                /\ pc' = [new_pc EXCEPT ![Waiter["who"]] = "Writing"]
                /\ holders' = [new_holders EXCEPT !["writer"] = Waiter["who"]]
                /\ lock_state' = [new_lock_state EXCEPT !["writer"] = TRUE]
                /\ wait_queue' = Tail(wait_queue)
            ELSE IF Waiter["for"] = "UpRead" THEN
                /\ pc' = [new_pc EXCEPT ![Waiter["who"]] = "UpReading"]
                /\ holders' = [new_holders EXCEPT !["upreader"] = Waiter["who"]]
                /\ lock_state' = [new_lock_state EXCEPT !["upread"] = TRUE]
                /\ wait_queue' = Tail(wait_queue)
            ELSE
                LET result == WakeAllReaders(wait_queue, new_pc, new_holders, new_lock_state) IN
                /\ pc' = result[1]
                /\ holders' = result[2]
                /\ lock_state' = result[3]
                /\ wait_queue' = result[4]
        ELSE
            /\ pc' = new_pc
            /\ holders' = new_holders
            /\ lock_state' = new_lock_state
            /\ wait_queue' = wait_queue

UpReadUnlock(t) ==
    /\ pc[t] = "UpReading"
    /\ LET
        new_pc == [pc EXCEPT ![t] = "Idle"]
        new_holders == [holders EXCEPT !["upreader"] = Nil]
        new_lock_state == [lock_state EXCEPT !["upread"] = FALSE]
        
        WakeCondition == Len(wait_queue) > 0
       IN
        IF WakeCondition THEN
            LET Waiter == Head(wait_queue) IN
            IF Waiter["for"] = "Write" /\ new_lock_state["readers"] = 0 THEN
                /\ pc' = [new_pc EXCEPT ![Waiter["who"]] = "Writing"]
                /\ holders' = [new_holders EXCEPT !["writer"] = Waiter["who"]]
                /\ lock_state' = [new_lock_state EXCEPT !["writer"] = TRUE]
                /\ wait_queue' = Tail(wait_queue)
            ELSE IF Waiter["for"] = "UpRead" THEN
                /\ pc' = [new_pc EXCEPT ![Waiter["who"]] = "UpReading"]
                /\ holders' = [new_holders EXCEPT !["upreader"] = Waiter["who"]]
                /\ lock_state' = [new_lock_state EXCEPT !["upread"] = TRUE]
                /\ wait_queue' = Tail(wait_queue)
            ELSE
                LET result == WakeAllReaders(wait_queue, new_pc, new_holders, new_lock_state) IN
                /\ pc' = result[1]
                /\ holders' = result[2]
                /\ lock_state' = result[3]
                /\ wait_queue' = result[4]
        ELSE
            /\ pc' = new_pc
            /\ holders' = new_holders
            /\ lock_state' = new_lock_state
            /\ wait_queue' = wait_queue

Next == \E t \in Threads:
    \/ ReadLock(t) \/ ReadWait(t)
    \/ WriteLock(t) \/ WriteWait(t)
    \/ UpReadLock(t) \/ UpReadWait(t)
    \/ ReadUnlock(t)
    \/ WriteUnlock(t)
    \/ UpReadUnlock(t)
    \/ Upgrade(t)
    \/ CompleteUpgrade(t)
    \/ Downgrade(t)

Fairness == \A t \in Threads:
    WF_vars(ReadUnlock(t))
    /\ WF_vars(WriteUnlock(t))
    /\ WF_vars(UpReadUnlock(t))
    /\ WF_vars(CompleteUpgrade(t))
    /\ WF_vars(Downgrade(t))

Spec == Init /\ [][Next]_vars /\ Fairness

====