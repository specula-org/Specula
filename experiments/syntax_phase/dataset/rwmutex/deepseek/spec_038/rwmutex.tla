---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads
OpType == {"read", "write", "upread"}
VARIABLES writer_holder, upreader_holder, reader_holds, reader_count, being_upgraded, wait_queue, waiting_op
vars == <<writer_holder, upreader_holder, reader_holds, reader_count, being_upgraded, wait_queue, waiting_op>>
Init == 
  writer_holder = {} 
  /\ upreader_holder = {} 
  /\ reader_holds = [t \in Threads |-> 0] 
  /\ reader_count = 0
  /\ being_upgraded = FALSE 
  /\ wait_queue = << >> 
  /\ waiting_op = [t \in Threads |-> "read"]
AcquireRead(t) == 
  /\ t \notin { wait_queue[i] : i \in 1..Len(wait_queue) }
  /\ IF writer_holder = {} /\ being_upgraded = FALSE THEN
      /\ reader_holds' = [reader_holds EXCEPT ![t] = reader_holds[t] + 1]
      /\ reader_count' = reader_count + 1
      /\ wait_queue' = wait_queue
      /\ waiting_op' = waiting_op
      /\ UNCHANGED <<writer_holder, upreader_holder, being_upgraded>>
    ELSE
      /\ wait_queue' = Append(wait_queue, t)
      /\ waiting_op' = [waiting_op EXCEPT ![t] = "read"]
      /\ UNCHANGED <<reader_holds, reader_count, writer_holder, upreader_holder, being_upgraded>>
AcquireWrite(t) == 
  /\ t \notin { wait_queue[i] : i \in 1..Len(wait_queue) }
  /\ IF writer_holder = {} /\ upreader_holder = {} /\ reader_count = 0 THEN
      /\ writer_holder' = {t}
      /\ wait_queue' = wait_queue
      /\ waiting_op' = waiting_op
      /\ UNCHANGED <<upreader_holder, reader_holds, reader_count, being_upgraded>>
    ELSE
      /\ wait_queue' = Append(wait_queue, t)
      /\ waiting_op' = [waiting_op EXCEPT ![t] = "write"]
      /\ UNCHANGED <<writer_holder, upreader_holder, reader_holds, reader_count, being_upgraded>>
AcquireUpread(t) == 
  /\ t \notin { wait_queue[i] : i \in 1..Len(wait_queue) }
  /\ IF writer_holder = {} /\ upreader_holder = {} THEN
      /\ upreader_holder' = {t}
      /\ wait_queue' = wait_queue
      /\ waiting_op' = waiting_op
      /\ UNCHANGED <<writer_holder, reader_holds, reader_count, being_upgraded>>
    ELSE
      /\ wait_queue' = Append(wait_queue, t)
      /\ waiting_op' = [waiting_op EXCEPT ![t] = "upread"]
      /\ UNCHANGED <<writer_holder, upreader_holder, reader_holds, reader_count, being_upgraded>>
ReleaseRead(t) == 
  /\ reader_holds[t] > 0
  /\ reader_holds' = [reader_holds EXCEPT ![t] = reader_holds[t] - 1]
  /\ reader_count' = reader_count - 1
  /\ IF reader_count' = 0 /\ wait_queue /= << >> THEN
      wait_queue' = Tail(wait_queue)
      /\ waiting_op' = waiting_op
    ELSE
      wait_queue' = wait_queue
      /\ waiting_op' = waiting_op
  /\ UNCHANGED <<writer_holder, upreader_holder, being_upgraded>>
ReleaseWrite(t) == 
  /\ writer_holder = {t}
  /\ writer_holder' = {}
  /\ wait_queue' = << >>
  /\ waiting_op' = waiting_op
  /\ UNCHANGED <<upreader_holder, reader_holds, reader_count, being_upgraded>>
ReleaseUpread(t) == 
  /\ upreader_holder = {t}
  /\ upreader_holder' = {}
  /\ wait_queue' = << >>
  /\ waiting_op' = waiting_op
  /\ UNCHANGED <<writer_holder, reader_holds, reader_count, being_upgraded>>
StartUpgrade(t) == 
  /\ upreader_holder = {t}
  /\ being_upgraded = FALSE
  /\ being_upgraded' = TRUE
  /\ UNCHANGED <<writer_holder, upreader_holder, reader_holds, reader_count, wait_queue, waiting_op>>
CompleteUpgrade(t) == 
  /\ upreader_holder = {t}
  /\ being_upgraded = TRUE
  /\ reader_count = 0
  /\ writer_holder' = {t}
  /\ upreader_holder' = {}
  /\ being_upgraded' = FALSE
  /\ wait_queue' = << >>
  /\ waiting_op' = waiting_op
  /\ reader_holds' = reader_holds
  /\ reader_count' = reader_count
Downgrade(t) == 
  /\ writer_holder = {t}
  /\ writer_holder' = {}
  /\ upreader_holder' = {t}
  /\ wait_queue' = << >>
  /\ waiting_op' = waiting_op
  /\ UNCHANGED <<reader_holds, reader_count, being_upgraded>>
Next == 
  \/ \E t \in Threads : AcquireRead(t)
  \/ \E t \in Threads : AcquireWrite(t)
  \/ \E t \in Threads : AcquireUpread(t)
  \/ \E t \in Threads : ReleaseRead(t)
  \/ \E t \in Threads : ReleaseWrite(t)
  \/ \E t \in Threads : ReleaseUpread(t)
  \/ \E t \in Threads : StartUpgrade(t)
  \/ \E t \in Threads : CompleteUpgrade(t)
  \/ \E t \in Threads : Downgrade(t)
Spec == Init /\ [][Next]_vars /\ 
  \A t \in Threads : 
    WF_vars(AcquireRead(t)) /\ WF_vars(AcquireWrite(t)) /\ WF_vars(AcquireUpread(t)) /\ 
    WF_vars(ReleaseRead(t)) /\ WF_vars(ReleaseWrite(t)) /\ WF_vars(ReleaseUpread(t)) /\ 
    WF_vars(StartUpgrade(t)) /\ WF_vars(CompleteUpgrade(t)) /\ WF_vars(Downgrade(t))
====