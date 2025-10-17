
---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads, null
VARIABLES lock, writer_thread, upreader_thread, readers, queue

TypeOK == 
  /\ lock \in [writer: BOOLEAN, upreader: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat]
  /\ writer_thread \in Threads \union {null}
  /\ upreader_thread \in Threads \union {null}
  /\ readers \subseteq Threads
  /\ queue \in Seq([thread: Threads, mode: {"read","write","upread"}])
  /\ (writer_thread # null) => 
        /\ lock.writer 
        /\ lock.upreader = FALSE 
        /\ lock.being_upgraded = FALSE 
        /\ lock.reader_count = 0
  /\ (upreader_thread # null) => 
        /\ lock.upreader 
        /\ ~lock.writer
  /\ lock.reader_count = Cardinality(readers)
  /\ \A t \in readers: 
        /\ t # writer_thread 
        /\ t # upreader_thread
  /\ \A t \in {m.thread: m \in queue}: 
        /\ t \notin readers 
        /\ t # writer_thread 
        /\ t # upreader_thread

Init == 
  /\ lock = [writer |-> FALSE, upreader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
  /\ writer_thread = null
  /\ upreader_thread = null
  /\ readers = {}
  /\ queue = <<>>

TryRead(t) == 
  /\ t \notin (readers \union {writer_thread, upreader_thread})
  /\ ~lock.writer
  /\ ~lock.being_upgraded
  /\ lock' = [lock EXCEPT !.reader_count = lock.reader_count + 1]
  /\ readers' = readers \union {t}
  /\ UNCHANGED <<writer_thread, upreader_thread, queue>>

TryWrite(t) == 
  /\ t \notin (readers \union {writer_thread, upreader_thread})
  /\ ~lock.writer
  /\ ~lock.upreader
  /\ ~lock.being_upgraded
  /\ lock.reader_count = 0
  /\ lock' = [lock EXCEPT !.writer = TRUE]
  /\ writer_thread' = t
  /\ UNCHANGED <<upreader_thread, readers, queue>>

TryUpRead(t) == 
  /\ t \notin (readers \union {writer_thread, upreader_thread})
  /\ ~lock.writer
  /\ ~lock.upreader
  /\ lock' = [lock EXCEPT !.upreader = TRUE]
  /\ upreader_thread' = t
  /\ UNCHANGED <<writer_thread, readers, queue>>

Enqueue(t, mode) == 
  /\ t \notin (readers \union {writer_thread, upreader_thread} \union {m.thread: m \in queue})
  /\ \/ (mode = "read") /\ ~(~lock.writer /\ ~lock.being_upgraded)
     \/ (mode = "write") /\ ~(~lock.writer /\ ~lock.upreader /\ ~lock.being_upgraded /\ lock.reader_count = 0)
     \/ (mode = "upread") /\ ~(~lock.writer /\ ~lock.upreader)
  /\ queue' = Append(queue, [thread |-> t, mode |-> mode])
  /\ UNCHANGED <<lock, writer_thread, upreader_thread, readers>>

ReleaseRead(t) == 
  /\ t \in readers
  /\ lock' = [lock EXCEPT !.reader_count = lock.reader_count - 1]
  /\ readers' = readers \ {t}
  /\ UNCHANGED <<writer_thread, upreader_thread, queue>>

ReleaseWrite(t) == 
  /\ writer_thread = t
  /\ lock' = [lock EXCEPT !.writer = FALSE]
  /\ writer_thread' = null
  /\ UNCHANGED <<upreader_thread, readers, queue>>

ReleaseUpRead(t) == 
  /\ upreader_thread = t
  /\ lock' = [lock EXCEPT !.upreader = FALSE]
  /\ upreader_thread' = null
  /\ UNCHANGED <<writer_thread, readers, queue>>

StartUpgrade(t) == 
  /\ upreader_thread = t
  /\ ~lock.being_upgraded
  /\ lock' = [lock EXCEPT !.being_upgraded = TRUE]
  /\ UNCHANGED <<writer_thread, upreader_thread, readers, queue>>

FinishUpgrade(t) == 
  /\ upreader_thread = t
  /\ lock.being_upgraded
  /\ lock.reader_count = 0
  /\ lock' = [lock EXCEPT !.being_upgraded = FALSE, !.upreader = FALSE, !.writer = TRUE]
  /\ writer_thread' = t
  /\ upreader_thread' = null
  /\ UNCHANGED <<readers, queue>>

Downgrade(t) == 
  /\ writer_thread = t
  /\ lock.writer
  /\ ~lock.upreader
  /\ lock' = [lock EXCEPT !.writer = FALSE, !.upreader = TRUE]
  /\ upreader_thread' = t
  /\ writer_thread' = null
  /\ UNCHANGED <<readers, queue>>

GrantFromQueue == 
  /\ queue # <<>>
  /\ LET head = Head(queue)
         t = head.thread
         mode = head.mode
     IN
     /\ \/ (mode = "read") /\ ~lock.writer /\ ~lock.being_upgraded
        \/ (mode = "write") /\ ~lock.writer /\ ~lock.upreader /\ ~lock.being_upgraded /\ lock.reader_count = 0
        \/ (mode = "upread") /\ ~lock.writer /\ ~lock.upreader
     /\ \/ (mode = "read") 
           /\ lock' = [lock EXCEPT !.reader_count = lock.reader_count + 1]
           /\ readers' = readers \union {t}
           /\ UNCHANGED <<writer_thread, upreader_thread>>
        \/ (mode = "write")
           /\ lock' = [lock EXCEPT !.writer = TRUE]
           /\ writer_thread' = t
           /\ UNCHANGED <<upreader_thread, readers>>
        \/ (mode = "upread")
           /\ lock' = [lock EXCEPT !.upreader = TRUE]
           /\ upreader_thread' = t
           /\ UNCHANGED <<writer_thread, readers>>
     /\ queue' = Tail(queue)

Next == 
  \/ \E t \in Threads : \/ TryRead(t)
                       \/ TryWrite(t)
                       \/ TryUpRead(t)
                       \/ Enqueue(t, "read")
                       \/ Enqueue(t, "write")
                       \/ Enqueue(t, "upread")
                       \/ ReleaseRead(t)
                       \/ ReleaseWrite(t)
                       \/ ReleaseUpRead(t)
                       \/ StartUpgrade(t)
                       \/ FinishUpgrade(t)
                       \/ Downgrade(t)
  \/ GrantFromQueue

Vars == <<lock, writer_thread, upreader_thread, readers, queue>>
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)
====