---- MODULE rwmutex ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANTS Procs
VARIABLES lock_state, wait_queue, active_readers, active_writer, active_upreader, upgrading
Vars == <<lock_state, wait_queue, active_readers, active_writer, active_upreader, upgrading>>
TypeOK == 
    /\ lock_state \in [writer: BOOLEAN, upgradeable_reader: BOOLEAN, being_upgraded: BOOLEAN, reader_count: Nat]
    /\ lock_state["reader_count"] \in 0..Cardinality(Procs)
    /\ wait_queue \in Seq([op: STRING, proc: Procs]) /\ \A e \in wait_queue: e["op"] \in {"read", "write", "upread"}
    /\ active_readers \in SUBSET Procs
    /\ active_writer \in SUBSET Procs /\ Cardinality(active_writer) <= 1
    /\ active_upreader \in SUBSET Procs /\ Cardinality(active_upreader) <= 1
    /\ upgrading \in BOOLEAN
Init == 
    /\ lock_state = [writer |-> FALSE, upgradeable_reader |-> FALSE, being_upgraded |-> FALSE, reader_count |-> 0]
    /\ wait_queue = <<>>
    /\ active_readers = {}
    /\ active_writer = {}
    /\ active_upreader = {}
    /\ upgrading = FALSE
CanRead == 
    ~lock_state["writer"] /\ ~lock_state["being_upgraded"]
CanWrite == 
    lock_state["reader_count"] = 0 /\ ~lock_state["writer"] /\ ~lock_state["upgradeable_reader"]
CanUpRead == 
    ~lock_state["writer"] /\ ~lock_state["upgradeable_reader"]
TryRead(proc) == 
    /\ CanRead
    /\ lock_state' = [lock_state EXCEPT !["reader_count"] = @ + 1]
    /\ active_readers' = active_readers \cup {proc}
    /\ UNCHANGED <<wait_queue, active_writer, active_upreader, upgrading>>
TryWrite(proc) == 
    /\ CanWrite
    /\ lock_state' = [lock_state EXCEPT !["writer"] = TRUE]
    /\ active_writer' = {proc}
    /\ UNCHANGED <<wait_queue, active_readers, active_upreader, upgrading>>
TryUpRead(proc) == 
    /\ CanUpRead
    /\ lock_state' = [lock_state EXCEPT !["upgradeable_reader"] = TRUE]
    /\ active_upreader' = {proc}
    /\ UNCHANGED <<wait_queue, active_readers, active_writer, upgrading>>
Enqueue(proc, op) == 
    /\ wait_queue' = Append(wait_queue, [op |-> op, proc |-> proc])
    /\ UNCHANGED <<lock_state, active_readers, active_writer, active_upreader, upgrading>>
Read(proc) == 
    \/ TryRead(proc)
    \/ Enqueue(proc, "read")
Write(proc) == 
    \/ TryWrite(proc)
    \/ Enqueue(proc, "write")
UpRead(proc) == 
    \/ TryUpRead(proc)
    \/ Enqueue(proc, "upread")
ReleaseRead(proc) == 
    /\ proc \in active_readers
    /\ lock_state' = [lock_state EXCEPT !["reader_count"] = @ - 1]
    /\ active_readers' = active_readers \ {proc}
    /\ \/ /\ lock_state["reader_count"] > 1
          /\ UNCHANGED wait_queue
       \/ /\ lock_state["reader_count"] = 1
          /\ IF wait_queue # <<>> 
             THEN LET head == Head(wait_queue) IN
                  /\ wait_queue' = Tail(wait_queue)
                  /\ ( head["op"] = "read" /\ TryRead(head["proc"])
                    \/ head["op"] = "write" /\ TryWrite(head["proc"])
                    \/ head["op"] = "upread" /\ TryUpRead(head["proc"]) )
             ELSE UNCHANGED wait_queue
    /\ UNCHANGED <<active_writer, active_upreader, upgrading>>
ReleaseWrite(proc) == 
    /\ proc \in active_writer
    /\ lock_state' = [lock_state EXCEPT !["writer"] = FALSE]
    /\ active_writer' = {}
    /\ IF wait_queue = <<>> THEN UNCHANGED wait_queue
       ELSE LET head == Head(wait_queue) IN
            /\ wait_queue' = Tail(wait_queue)
            /\ ( head["op"] = "read" /\ TryRead(head["proc"])
              \/ head["op"] = "write" /\ TryWrite(head["proc"])
              \/ head["op"] = "upread" /\ TryUpRead(head["proc"]) )
    /\ UNCHANGED <<active_readers, active_upreader, upgrading>>
ReleaseUpRead(proc) == 
    /\ proc \in active_upreader
    /\ lock_state' = [lock_state EXCEPT !["upgradeable_reader"] = FALSE]
    /\ active_upreader' = {}
    /\ \/ /\ (lock_state["reader_count"] > 0 \/ lock_state["writer"] \/ lock_state["being_upgraded"])
          /\ UNCHANGED wait_queue
       \/ /\ lock_state["reader_count"] = 0 /\ ~lock_state["writer"] /\ ~lock_state["being_upgraded"]
          /\ IF wait_queue = <<>> THEN UNCHANGED wait_queue
             ELSE LET head == Head(wait_queue) IN
                  /\ wait_queue' = Tail(wait_queue)
                  /\ ( head["op"] = "read" /\ TryRead(head["proc"])
                    \/ head["op"] = "write" /\ TryWrite(head["proc"])
                    \/ head["op"] = "upread" /\ TryUpRead(head["proc"]) )
    /\ UNCHANGED <<active_readers, active_writer, upgrading>>
Upgrade(proc) == 
    /\ proc \in active_upreader
    /\ ~upgrading
    /\ lock_state["reader_count"] = 0
    /\ lock_state' = [lock_state EXCEPT !["writer"] = TRUE, !["upgradeable_reader"] = FALSE, !["being_upgraded"] = FALSE]
    /\ active_writer' = {proc}
    /\ active_upreader' = {}
    /\ upgrading' = FALSE
    /\ UNCHANGED <<wait_queue, active_readers>>
Downgrade(proc) == 
    /\ proc \in active_writer
    /\ lock_state' = [lock_state EXCEPT !["writer"] = FALSE, !["upgradeable_reader"] = TRUE]
    /\ active_writer' = {}
    /\ active_upreader' = {proc}
    /\ UNCHANGED <<wait_queue, active_readers, upgrading>>
Next == 
    \/ \E proc \in Procs: Read(proc)
    \/ \E proc \in Procs: Write(proc)
    \/ \E proc \in Procs: UpRead(proc)
    \/ \E proc \in Procs: ReleaseRead(proc)
    \/ \E proc \in Procs: ReleaseWrite(proc)
    \/ \E proc \in Procs: ReleaseUpRead(proc)
    \/ \E proc \in Procs: Upgrade(proc)
    \/ \E proc \in Procs: Downgrade(proc)
Spec == 
    /\ Init
    /\ [][Next]_Vars
    /\ WF_Vars(Next)
====