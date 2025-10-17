---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Proc, NULL
ASSUME NULL \notin Proc
VARIABLES writer, upread_holder, readers, being_upgraded, wait_queue
TypeOK == 
  /\ writer \in Proc \cup {NULL}
  /\ upread_holder \in Proc \cup {NULL}
  /\ readers \subseteq Proc
  /\ being_upgraded \in BOOLEAN
  /\ wait_queue \in Seq([proc: Proc, op: {"read", "write", "upread"}])
  /\ (writer # NULL => upread_holder = NULL /\ readers = {} /\ ~being_upgraded)
  /\ (upread_holder # NULL => writer = NULL /\ upread_holder \in readers)
  /\ (being_upgraded => upread_holder # NULL)
Init == 
  /\ writer = NULL
  /\ upread_holder = NULL
  /\ readers = {}
  /\ being_upgraded = FALSE
  /\ wait_queue = <<>>
ReadAcquire(p) == 
  /\ p \notin readers
  /\ writer # p
  /\ upread_holder # p
  /\ \A elem \in ToSet(wait_queue) : elem.proc # p
  /\ IF writer = NULL /\ ~being_upgraded
     THEN /\ readers' = readers \cup {p}
          /\ UNCHANGED <<writer, upread_holder, being_upgraded, wait_queue>>
     ELSE /\ wait_queue' = Append(wait_queue, [proc |-> p, op |-> "read"])
          /\ UNCHANGED <<writer, upread_holder, readers, being_upgraded>>
WriteAcquire(p) == 
  /\ p \notin readers
  /\ writer # p
  /\ upread_holder # p
  /\ \A elem \in ToSet(wait_queue) : elem.proc # p
  /\ IF writer = NULL /\ upread_holder = NULL /\ readers = {} /\ ~being_upgraded
     THEN /\ writer' = p
          /\ UNCHANGED <<upread_holder, readers, being_upgraded, wait_queue>>
     ELSE /\ wait_queue' = Append(wait_queue, [proc |-> p, op |-> "write"])
          /\ UNCHANGED <<writer, upread_holder, readers, being_upgraded>>
UpreadAcquire(p) == 
  /\ p \notin readers
  /\ writer # p
  /\ upread_holder # p
  /\ \A elem \in ToSet(wait_queue) : elem.proc # p
  /\ IF writer = NULL /\ upread_holder = NULL /\ ~being_upgraded
     THEN /\ upread_holder' = p
          /\ readers' = readers \cup {p}
          /\ UNCHANGED <<writer, being_upgraded, wait_queue>>
     ELSE /\ wait_queue' = Append(wait_queue, [proc |-> p, op |-> "upread"])
          /\ UNCHANGED <<writer, upread_holder, readers, being_upgraded>>
FinishRead(p) == 
  /\ p \in readers
  /\ readers' = readers \ {p}
  /\ IF p = upread_holder THEN upread_holder' = NULL ELSE UNCHANGED upread_holder
  /\ IF wait_queue # <<>> 
     THEN wait_queue' = Tail(wait_queue)
     ELSE wait_queue' = wait_queue
  /\ UNCHANGED <<writer, being_upgraded>>
FinishWrite(p) == 
  /\ writer = p
  /\ writer' = NULL
  /\ wait_queue' = <<>>
  /\ UNCHANGED <<upread_holder, readers, being_upgraded>>
FinishUpread(p) == 
  /\ upread_holder = p
  /\ upread_holder' = NULL
  /\ readers' = readers \ {p}
  /\ wait_queue' = <<>>
  /\ UNCHANGED <<writer, being_upgraded>>
StartUpgrade(p) == 
  /\ upread_holder = p
  /\ ~being_upgraded
  /\ being_upgraded' = TRUE
  /\ UNCHANGED <<writer, upread_holder, readers, wait_queue>>
CompleteUpgrade(p) == 
  /\ being_upgraded
  /\ upread_holder = p
  /\ readers = {p}
  /\ being_upgraded' = FALSE
  /\ writer' = p
  /\ upread_holder' = NULL
  /\ readers' = readers \ {p}
  /\ UNCHANGED wait_queue
Downgrade(p) == 
  /\ writer = p
  /\ writer' = NULL
  /\ upread_holder' = p
  /\ readers' = readers \cup {p}
  /\ being_upgraded' = FALSE
  /\ UNCHANGED wait_queue
Next == 
  \/ \E p \in Proc : ReadAcquire(p)
  \/ \E p \in Proc : WriteAcquire(p)
  \/ \E p \in Proc : UpreadAcquire(p)
  \/ \E p \in Proc : FinishRead(p)
  \/ \E p \in Proc : FinishWrite(p)
  \/ \E p \in Proc : FinishUpread(p)
  \/ \E p \in Proc : StartUpgrade(p)
  \/ \E p \in Proc : CompleteUpgrade(p)
  \/ \E p \in Proc : Downgrade(p)
UnlockActions == \E p \in Proc : FinishRead(p) \/ FinishWrite(p) \/ FinishUpread(p)
AcquireActions == \E p \in Proc : ReadAcquire(p) \/ WriteAcquire(p) \/ UpreadAcquire(p)
UpgradeActions == \E p \in Proc : StartUpgrade(p) \/ CompleteUpgrade(p) \/ Downgrade(p)
Spec == Init /\ [][Next]_<<writer, upread_holder, readers, being_upgraded, wait_queue>> 
         /\ WF_<<writer, upread_holder, readers, being_upgraded, wait_queue>>(UnlockActions)
         /\ WF_<<writer, upread_holder, readers, being_upgraded, wait_queue>>(AcquireActions)
         /\ WF_<<writer, upread_holder, readers, being_upgraded, wait_queue>>(UpgradeActions)
====