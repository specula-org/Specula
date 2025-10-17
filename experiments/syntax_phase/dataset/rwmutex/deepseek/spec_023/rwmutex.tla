---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANTS PID, NULL
VARIABLES lock, queue, holders, upgrading
vars == <<lock, queue, holders, upgrading>>
TypeOK == 
    /\ lock = [writer |-> BOOLEAN, upread |-> BOOLEAN, being_upgraded |-> BOOLEAN, reader_count |-> Nat]
    /\ queue \in Seq(PID \times {"read", "write", "upread"})
    /\ holders = [readers |-> SUBSET PID, writer |-> PID \cup {NULL}, upreader |-> PID \cup {NULL}]
    /\ upgrading \in PID \cup {NULL}
    /\ (holders["writer"] # NULL => lock["writer"])
    /\ (holders["upreader"] # NULL => lock["upread"])
    /\ Cardinality(holders["readers"]) = lock["reader_count"]
    /\ (upgrading # NULL => lock["being_upgraded"])
Init == 
    /\ lock = [writer |-> FALSE, upread |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ queue = <<>>
    /\ holders = [readers |-> {}, writer |-> NULL, upreader |-> NULL]
    /\ upgrading = NULL
CanRead(p) == 
    p \notin holders["readers"] /\ p # holders["writer"] /\ p # holders["upreader"] /\ \A q \in DOMAIN queue: queue[q][1] # p
ReadAcquire(p) == 
    /\ CanRead(p)
    /\ ~lock["writer"] /\ ~lock["being_upgraded"]
    /\ lock' = [lock EXCEPT !.reader_count = @ + 1]
    /\ holders' = [holders EXCEPT !.readers = @ \cup {p}]
    /\ UNCHANGED <<queue, upgrading>>
ReadEnqueue(p) == 
    /\ CanRead(p)
    /\ lock["writer"] \/ lock["being_upgraded"]
    /\ queue' = Append(queue, <<p, "read">>)
    /\ UNCHANGED <<lock, holders, upgrading>>
WriteAcquire(p) == 
    /\ p \notin holders["readers"] /\ p # holders["writer"] /\ p # holders["upreader"]
    /\ \A q \in DOMAIN queue: queue[q][1] # p
    /\ ~lock["writer"] /\ ~lock["upread"] /\ lock["reader_count"] = 0
    /\ lock' = [lock EXCEPT !.writer = TRUE]
    /\ holders' = [holders EXCEPT !.writer = p]
    /\ UNCHANGED <<queue, upgrading>>
WriteEnqueue(p) == 
    /\ p \notin holders["readers"] /\ p # holders["writer"] /\ p # holders["upreader"]
    /\ \A q \in DOMAIN queue: queue[q][1] # p
    /\ lock["writer"] \/ lock["upread"] \/ lock["reader_count"] > 0
    /\ queue' = Append(queue, <<p, "write">>)
    /\ UNCHANGED <<lock, holders, upgrading>>
UpreadAcquire(p) == 
    /\ p \notin holders["readers"] /\ p # holders["writer"] /\ p # holders["upreader"]
    /\ \A q \in DOMAIN queue: queue[q][1] # p
    /\ ~lock["writer"] /\ ~lock["upread"]
    /\ lock' = [lock EXCEPT !.upread = TRUE]
    /\ holders' = [holders EXCEPT !.upreader = p]
    /\ UNCHANGED <<queue, upgrading>>
UpreadEnqueue(p) == 
    /\ p \notin holders["readers"] /\ p # holders["writer"] /\ p # holders["upreader"]
    /\ \A q \in DOMAIN queue: queue[q][1] # p
    /\ lock["writer"] \/ lock["upread"]
    /\ queue' = Append(queue, <<p, "upread">>)
    /\ UNCHANGED <<lock, holders, upgrading>>
ReadRelease(p) == 
    /\ p \in holders["readers"]
    /\ LET new_readers == holders["readers"] \ {p} IN
        LET lock_after_release == [lock EXCEPT !.reader_count = lock["reader_count"] - 1] IN
        IF new_readers = {} 
        THEN \/ \E pos \in DOMAIN queue: 
                LET wproc == queue[pos] IN
                /\ ( (wproc[2] = "read" /\ ~lock_after_release["writer"] /\ ~lock_after_release["being_upgraded"]) \/
                    (wproc[2] = "write" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"] /\ lock_after_release["reader_count"] = 0) \/
                    (wproc[2] = "upread" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"]) )
                /\ IF wproc[2] = "read" 
                   THEN /\ lock' = [lock_after_release EXCEPT !.reader_count = @ + 1]
                        /\ holders' = [holders EXCEPT !.readers = new_readers \cup {wproc[1]}]
                   ELSE IF wproc[2] = "write" 
                        THEN /\ lock' = [lock_after_release EXCEPT !.writer = TRUE]
                             /\ holders' = [holders EXCEPT !.readers = new_readers, !.writer = wproc[1]]
                        ELSE IF wproc[2] = "upread" 
                             THEN /\ lock' = [lock_after_release EXCEPT !.upread = TRUE]
                                  /\ holders' = [holders EXCEPT !.readers = new_readers, !.upreader = wproc[1]]
                /\ queue' = IF pos = 1 THEN SubSeq(queue, 2, Len(queue)) 
                           ELSE IF pos = Len(queue) THEN SubSeq(queue, 1, Len(queue)-1)
                           ELSE Append(SubSeq(queue, 1, pos-1), SubSeq(queue, pos+1, Len(queue)))
        ELSE /\ lock' = lock_after_release
             /\ holders' = [holders EXCEPT !.readers = new_readers]
             /\ queue' = queue
    /\ UNCHANGED upgrading
WriteRelease(p) == 
    /\ holders["writer"] = p
    /\ LET lock_after_release == [lock EXCEPT !.writer = FALSE] IN
        LET holders_after_release == [holders EXCEPT !.writer = NULL] IN
        \/ \E pos \in DOMAIN queue: 
             LET wproc == queue[pos] IN
             ( (wproc[2] = "read" /\ ~lock_after_release["writer"] /\ ~lock_after_release["being_upgraded"]) \/
               (wproc[2] = "write" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"] /\ lock_after_release["reader_count"] = 0) \/
               (wproc[2] = "upread" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"]) )
             /\ IF wproc[2] = "read" 
                THEN lock' = [lock_after_release EXCEPT !.reader_count = @ + 1]
                     holders' = [holders_after_release EXCEPT !.readers = @ \cup {wproc[1]}]
                ELSE IF wproc[2] = "write" 
                     THEN lock' = [lock_after_release EXCEPT !.writer = TRUE]
                          holders' = [holders_after_release EXCEPT !.writer = wproc[1]]
                ELSE IF wproc[2] = "upread" 
                     THEN lock' = [lock_after_release EXCEPT !.upread = TRUE]
                          holders' = [holders_after_release EXCEPT !.upreader = wproc[1]]
             /\ queue' = IF pos = 1 THEN SubSeq(queue, 2, Len(queue)) 
                        ELSE IF pos = Len(queue) THEN SubSeq(queue, 1, Len(queue)-1)
                        ELSE Append(SubSeq(queue, 1, pos-1), SubSeq(queue, pos+1, Len(queue)))
        \/ ~\E pos \in DOMAIN queue : ( (queue[pos][2] = "read" /\ ~lock_after_release["writer"] /\ ~lock_after_release["being_upgraded"]) \/
                                      (queue[pos][2] = "write" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"] /\ lock_after_release["reader_count"] = 0) \/
                                      (queue[pos][2] = "upread" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"]) )
             /\ lock' = lock_after_release
             /\ holders' = holders_after_release
             /\ queue' = queue
    /\ UNCHANGED upgrading
UpreadRelease(p) == 
    /\ holders["upreader"] = p
    /\ LET lock_after_release == [lock EXCEPT !.upread = FALSE] IN
        LET holders_after_release == [holders EXCEPT !.upreader = NULL] IN
        \/ \E pos \in DOMAIN queue: 
             LET wproc == queue[pos] IN
             ( (wproc[2] = "read" /\ ~lock_after_release["writer"] /\ ~lock_after_release["being_upgraded"]) \/
               (wproc[2] = "write" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"] /\ lock_after_release["reader_count"] = 0) \/
               (wproc[2] = "upread" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"]) )
             /\ IF wproc[2] = "read" 
                THEN lock' = [lock_after_release EXCEPT !.reader_count = @ + 1]
                     holders' = [holders_after_release EXCEPT !.readers = @ \cup {wproc[1]}]
                ELSE IF wproc[2] = "write" 
                     THEN lock' = [lock_after_release EXCEPT !.writer = TRUE]
                          holders' = [holders_after_release EXCEPT !.writer = wproc[1]]
                ELSE IF wproc[2] = "upread" 
                     THEN lock' = [lock_after_release EXCEPT !.upread = TRUE]
                          holders' = [holders_after_release EXCEPT !.upreader = wproc[1]]
             /\ queue' = IF pos = 1 THEN SubSeq(queue, 2, Len(queue)) 
                        ELSE IF pos = Len(queue) THEN SubSeq(queue, 1, Len(queue)-1)
                        ELSE Append(SubSeq(queue, 1, pos-1), SubSeq(queue, pos+1, Len(queue)))
        \/ ~\E pos \in DOMAIN queue : ( (queue[pos][2] = "read" /\ ~lock_after_release["writer"] /\ ~lock_after_release["being_upgraded"]) \/
                                      (queue[pos][2] = "write" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"] /\ lock_after_release["reader_count"] = 0) \/
                                      (queue[pos][2] = "upread" /\ ~lock_after_release["writer"] /\ ~lock_after_release["upread"]) )
             /\ lock' = lock_after_release
             /\ holders' = holders_after_release
             /\ queue' = queue
    /\ UNCHANGED upgrading
Upgrade(p) == 
    /\ holders["upreader"] = p
    /\ upgrading' = p
    /\ lock' = [lock EXCEPT !.being_upgraded = TRUE]
    /\ UNCHANGED <<queue, holders>>
CompleteUpgrade(p) == 
    /\ upgrading = p
    /\ lock["reader_count"] = 0
    /\ upgrading' = NULL
    /\ lock' = [lock EXCEPT !.being_upgraded = FALSE, !.upread = FALSE, !.writer = TRUE]
    /\ holders' = [holders EXCEPT !.upreader = NULL, !.writer = p]
    /\ UNCHANGED queue
Downgrade(p) == 
    /\ holders["writer"] = p
    /\ lock' = [lock EXCEPT !.writer = FALSE, !.upread = TRUE]
    /\ holders' = [holders EXCEPT !.writer = NULL, !.upreader = p]
    /\ UNCHANGED <<queue, upgrading>>
Next == 
    \/ \E p \in PID: ReadAcquire(p) \/ ReadEnqueue(p)
    \/ \E p \in PID: WriteAcquire(p) \/ WriteEnqueue(p)
    \/ \E p \in PID: UpreadAcquire(p) \/ UpreadEnqueue(p)
    \/ \E p \in PID: ReadRelease(p)
    \/ \E p \in PID: WriteRelease(p)
    \/ \E p \in PID: UpreadRelease(p)
    \/ \E p \in PID: Upgrade(p)
    \/ \E p \in PID: CompleteUpgrade(p)
    \/ \E p \in PID: Downgrade(p)
Spec == Init /\ [][Next]_vars /\ WF_vars(ReadRelease) /\ WF_vars(WriteRelease) /\ WF_vars(UpreadRelease) /\ WF_vars(CompleteUpgrade)
====