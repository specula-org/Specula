---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Threads

ASSUME Threads \subseteq {"t1", "t2", "t3"}

VARIABLES lock, holders, pc, pending_type, wait_queue

Vars == <<lock, holders, pc, pending_type, wait_queue>>

None == "none"
RequestTypes == {"read", "write", "upread"}

Init ==
    /\ lock = [writer_bit |-> FALSE, upreader_bit |-> FALSE, upgrading_bit |-> FALSE, reader_count |-> 0]
    /\ holders = [writer |-> None, upreader |-> None, readers |-> {}]
    /\ pc = [t \in Threads |-> "idle"]
    /\ pending_type = [t \in Threads |-> None]
    /\ wait_queue = <<>>

Request(t, type) ==
    /\ pc[t] = "idle"
    /\ type \in RequestTypes
    /\ pc' = [pc EXCEPT ![t] = "pending"]
    /\ pending_type' = [pending_type EXCEPT ![t] = type]
    /\ UNCHANGED <<lock, holders, wait_queue>>

TryAcquire(t) ==
    LET current_req_type == pending_type[t] IN
    /\ pc[t] = "pending"
    /\ t \notin SeqToSet(wait_queue)
    /\ \/ /\ current_req_type = "read"
           /\ IF ~lock.writer_bit /\ ~lock.upgrading_bit
              THEN /\ lock' = [lock EXCEPT !.reader_count = @ + 1]
                   /\ holders' = [holders EXCEPT !.readers = @ \cup {t}]
                   /\ pc' = [pc EXCEPT ![t] = "reading"]
                   /\ pending_type' = [pending_type EXCEPT ![t] = None]
                   /\ UNCHANGED <<wait_queue>>
              ELSE /\ wait_queue' = Append(wait_queue, t)
                   /\ UNCHANGED <<lock, holders, pc, pending_type>>
        \/ /\ current_req_type = "write"
           /\ IF ~lock.writer_bit /\ ~lock.upreader_bit /\ lock.reader_count = 0
              THEN /\ lock' = [lock EXCEPT !.writer_bit = TRUE]
                   /\ holders' = [holders EXCEPT !.writer = t]
                   /\ pc' = [pc EXCEPT ![t] = "writing"]
                   /\ pending_type' = [pending_type EXCEPT ![t] = None]
                   /\ UNCHANGED <<wait_queue>>
              ELSE /\ wait_queue' = Append(wait_queue, t)
                   /\ UNCHANGED <<lock, holders, pc, pending_type>>
        \/ /\ current_req_type = "upread"
           /\ IF ~lock.writer_bit /\ ~lock.upreader_bit
              THEN /\ lock' = [lock EXCEPT !.upreader_bit = TRUE]
                   /\ holders' = [holders EXCEPT !.upreader = t]
                   /\ pc' = [pc EXCEPT ![t] = "upreading"]
                   /\ pending_type' = [pending_type EXCEPT ![t] = None]
                   /\ UNCHANGED <<wait_queue>>
              ELSE /\ wait_queue' = Append(wait_queue, t)
                   /\ UNCHANGED <<lock, holders, pc, pending_type>>

ProcessQueue ==
    /\ Len(wait_queue) > 0
    /\ LET t = Head(wait_queue)
           current_req_type = pending_type[t]
       IN
        \/ /\ current_req_type = "read"
           /\ ~lock.writer_bit /\ ~lock.upgrading_bit
           /\ lock' = [lock EXCEPT !.reader_count = @ + 1]
           /\ holders' = [holders EXCEPT !.readers = @ \cup {t}]
           /\ pc' = [pc EXCEPT ![t] = "reading"]
           /\ pending_type' = [pending_type EXCEPT ![t] = None]
           /\ wait_queue' = Tail(wait_queue)
        \/ /\ current_req_type = "write"
           /\ ~lock.writer_bit /\ ~lock.upreader_bit /\ lock.reader_count = 0
           /\ lock' = [lock EXCEPT !.writer_bit = TRUE]
           /\ holders' = [holders EXCEPT !.writer = t]
           /\ pc' = [pc EXCEPT ![t] = "writing"]
           /\ pending_type' = [pending_type EXCEPT ![t] = None]
           /\ wait_queue' = Tail(wait_queue)
        \/ /\ current_req_type = "upread"
           /\ ~lock.writer_bit /\ ~lock.upreader_bit
           /\ lock' = [lock EXCEPT !.upreader_bit = TRUE]
           /\ holders' = [holders EXCEPT !.upreader = t]
           /\ pc' = [pc EXCEPT ![t] = "upreading"]
           /\ pending_type' = [pending_type EXCEPT ![t] = None]
           /\ wait_queue' = Tail(wait_queue)

ReleaseRead(t) ==
    /\ pc[t] = "reading"
    /\ t \in holders.readers
    /\ lock' = [lock EXCEPT !.reader_count = @ - 1]
    /\ holders' = [holders EXCEPT !.readers = @ \ {t}]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<pending_type, wait_queue>>

ReleaseWrite(t) ==
    /\ pc[t] = "writing"
    /\ holders.writer = t
    /\ lock' = [lock EXCEPT !.writer_bit = FALSE]
    /\ holders' = [holders EXCEPT !.writer = None]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<pending_type, wait_queue>>

ReleaseUpread(t) ==
    /\ pc[t] = "upreading"
    /\ holders.upreader = t
    /\ lock' = [lock EXCEPT !.upreader_bit = FALSE]
    /\ holders' = [holders EXCEPT !.upreader = None]
    /\ pc' = [pc EXCEPT ![t] = "idle"]
    /\ UNCHANGED <<pending_type, wait_queue>>

StartUpgrade(t) ==
    /\ pc[t] = "upreading"
    /\ holders.upreader = t
    /\ lock' = [lock EXCEPT !.upgrading_bit = TRUE]
    /\ pc' = [pc EXCEPT ![t] = "upgrading"]
    /\ UNCHANGED <<holders, pending_type, wait_queue>>

FinishUpgrade(t) ==
    /\ pc[t] = "upgrading"
    /\ holders.upreader = t
    /\ lock.reader_count = 0
    /\ lock' = [lock EXCEPT !.writer_bit = TRUE, !.upreader_bit = FALSE, !.upgrading_bit = FALSE]
    /\ holders' = [holders EXCEPT !.writer = t, !.upreader = None]
    /\ pc' = [pc EXCEPT ![t] = "writing"]
    /\ UNCHANGED <<pending_type, wait_queue>>

Downgrade(t) ==
    /\ pc[t] = "writing"
    /\ holders.writer = t
    /\ lock' = [lock EXCEPT !.writer_bit = FALSE, !.upreader_bit = TRUE]
    /\ holders' = [holders EXCEPT !.writer = None, !.upreader = t]
    /\ pc' = [pc EXCEPT ![t] = "upreading"]
    /\ UNCHANGED <<pending_type, wait_queue>>

Next ==
    \/ (\E t \in Threads, type \in RequestTypes: Request(t, type))
    \/ (\E t \in Threads: TryAcquire(t))
    \/ ProcessQueue
    \/ (\E t \in Threads: ReleaseRead(t))
    \/ (\E t \in Threads: ReleaseWrite(t))
    \/ (\E t \in Threads: ReleaseUpread(t))
    \/ (\E t \in Threads: StartUpgrade(t))
    \/ (\E t \in Threads: FinishUpgrade(t))
    \/ (\E t \in Threads: Downgrade(t))

TypeOK ==
    /\ lock \in [writer_bit: BOOLEAN, upreader_bit: BOOLEAN, upgrading_bit: BOOLEAN, reader_count: Nat]
    /\ holders \in [writer: Threads \cup {None}, upreader: Threads \cup {None}, readers: SUBSET Threads]
    /\ pc \in [Threads -> {"idle", "pending", "reading", "writing", "upreading", "upgrading"}]
    /\ pending_type \in [Threads -> RequestTypes \cup {None}]
    /\ wait_queue \in Seq(Threads)

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====
