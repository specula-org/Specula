
---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS THREADS, MaxReader
VARIABLES lock, upgrading, queue, guards

(* State representation *)
Lock == [writer: {0,1}, upreader: {0,1}, being_upgraded: {0,1}, reader_count: 0..MaxReader]

TypeOK ==
  lock \in Lock
  /\ upgrading \in THREADS \cup {NULL}
  /\ queue \in Seq(THREADS \times {"read", "write", "upread"})
  /\ guards \in Bag(THREADS \times {"read", "write", "upread"})

Init ==
  lock == [writer |-> 0, upreader |-> 0, being_upgraded |-> 0, reader_count |-> 0]
  /\ upgrading = NULL
  /\ queue = <<>>
  /\ guards = EmptyBag

(* Helper: Thread not waiting in queue *)
NotWaiting(thread) == thread \notin { t: t \in DOMAIN queue }

(* Read acquisition *)
TryRead(thread) ==
  NotWaiting(thread)
  /\ LET new_count == lock.reader_count + 1 IN
     IF lock.writer = 0 /\ lock.being_upgraded = 0 /\ new_count <= MaxReader
     THEN lock' = [lock EXCEPT !.reader_count = new_count]
          /\ guards' = guards (+) {<<thread, "read">>}
          /\ UNCHANGED <<queue, upgrading>>
     ELSE queue' = Append(queue, <<thread, "read">>)
         /\ UNCHANGED <<lock, guards, upgrading>>
  ENDIF

(* Write acquisition *)
TryWrite(thread) ==
  NotWaiting(thread)
  /\ IF lock = [writer |-> 0, upreader |-> 0, being_upgraded |-> 0, reader_count |-> 0]
     THEN lock' = [lock EXCEPT !.writer = 1]
          /\ guards' = guards (+) {<<thread, "write">>}
          /\ UNCHANGED <<queue, upgrading>>
     ELSE queue' = Append(queue, <<thread, "write">>)
         /\ UNCHANGED <<lock, guards, upgrading>>
  ENDIF

(* Upgradeable read acquisition *)
TryUpread(thread) ==
  NotWaiting(thread)
  /\ LET old_lock == lock IN
     IF old_lock.writer = 0 /\ old_lock.upreader = 0
     THEN lock' = [old_lock EXCEPT !.upreader = 1]
          /\ guards' = guards (+) {<<thread, "upread">>}
          /\ UNCHANGED <<queue, upgrading>>
     ELSE queue' = Append(queue, <<thread, "upread">>)
         /\ UNCHANGED <<lock, guards, upgrading>>
  ENDIF

(* Read release *)
ReleaseRead(thread) ==
  /\ <<thread, "read">> \in guards
  /\ guards' = guards (-) {<<thread, "read">>}
  /\ lock' = [lock EXCEPT !.reader_count = lock.reader_count - 1]
  /\ IF lock.reader_count = 1 (* Will become 0 after release *)
     THEN IF queue = <<>> THEN UNCHANGED queue
          ELSE queue' = Tail(queue)
     ELSE UNCHANGED queue
  /\ UNCHANGED upgrading

(* Write release *)
ReleaseWrite(thread) ==
  /\ <<thread, "write">> \in guards
  /\ guards' = guards (-) {<<thread, "write">>}
  /\ lock' = [lock EXCEPT !.writer = 0]
  /\ queue' = <<>> (* Wake all *)
  /\ UNCHANGED upgrading

(* Upgradeable read release *)
ReleaseUpread(thread) ==
  /\ <<thread, "upread">> \in guards
  /\ guards' = guards (-) {<<thread, "upread">>}
  /\ lock' = [lock EXCEPT !.upreader = 0]
  /\ IF lock = [writer |-> 0, upreader |-> 1, being_upgraded |-> 0, reader_count |-> 0]
     THEN queue' = <<>> (* Wake all if only upreader present *)
     ELSE UNCHANGED queue
  /\ UNCHANGED upgrading

(* Start upgrade process *)
StartUpgrade(thread) ==
  /\ <<thread, "upread">> \in guards
  /\ upgrading = NULL
  /\ lock' = [lock EXCEPT !.being_upgraded = 1]
  /\ upgrading' = thread
  /\ UNCHANGED <<queue, guards>>

(* Finish upgrade process *)
FinishUpgrade(thread) ==
  /\ upgrading = thread
  /\ lock.reader_count = 0
  /\ lock.writer = 0
  /\ lock.upreader = 1
  /\ lock.being_upgraded = 1
  /\ lock' = [lock EXCEPT !.writer = 1, !.upreader = 0, !.being_upgraded = 0]
  /\ guards' = (guards (-) {<<thread, "upread">>}) (+) {<<thread, "write">>}
  /\ upgrading' = NULL
  /\ UNCHANGED queue

(* Downgrade writer to upgradeable reader *)
Downgrade(thread) ==
  /\ <<thread, "write">> \in guards
  /\ lock.writer = 1
  /\ lock.upreader = 0
  /\ lock' = [lock EXCEPT !.writer = 0, !.upreader = 1]
  /\ guards' = (guards (-) {<<thread, "write">>}) (+) {<<thread, "upread">>}
  /\ UNCHANGED <<queue, upgrading>>

(* Next-state relation *)
Next ==
  \/ \E thread \in THREADS: TryRead(thread)
  \/ \E thread \in THREADS: TryWrite(thread)
  \/ \E thread \in THREADS: TryUpread(thread)
  \/ \E thread \in THREADS: ReleaseRead(thread)
  \/ \E thread \in THREADS: ReleaseWrite(thread)
  \/ \E thread \in THREADS: ReleaseUpread(thread)
  \/ \E thread \in THREADS: StartUpgrade(thread)
  \/ \E thread \in THREADS: FinishUpgrade(thread)
  \/ \E thread \in THREADS: Downgrade(thread)

Vars == <<lock, upgrading, queue, guards>>
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

====