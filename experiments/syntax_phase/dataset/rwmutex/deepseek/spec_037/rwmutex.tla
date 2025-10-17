---- MODULE rwmutex ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
VARIABLES writer, upreader, being_upgraded, reader_count, queue
vars == <<writer, upreader, being_upgraded, reader_count, queue>>
TypeOK == 
  /\ reader_count \in Nat
  /\ writer \in BOOLEAN
  /\ upreader \in BOOLEAN
  /\ being_upgraded \in BOOLEAN
  /\ queue \in Seq({"read", "write", "upread"})
Init == 
  /\ writer = FALSE
  /\ upreader = FALSE
  /\ being_upgraded = FALSE
  /\ reader_count = 0
  /\ queue = << >>
ReadAcquire == 
  IF writer = FALSE /\ being_upgraded = FALSE
  THEN 
    reader_count' = reader_count + 1
    /\ UNCHANGED <<writer, upreader, being_upgraded, queue>>  \* Added UNCHANGED for variables not modified
  ELSE 
    queue' = Append(queue, "read")
    /\ UNCHANGED <<writer, upreader, being_upgraded, reader_count>>  \* Added UNCHANGED for variables not modified
WriteAcquire == 
  IF writer = FALSE /\ upreader = FALSE /\ reader_count = 0 /\ being_upgraded = FALSE
  THEN 
    writer' = TRUE
    /\ UNCHANGED <<upreader, being_upgraded, reader_count, queue>>  \* Added UNCHANGED for variables not modified
  ELSE 
    queue' = Append(queue, "write")
    /\ UNCHANGED <<writer, upreader, being_upgraded, reader_count>>  \* Added UNCHANGED for variables not modified
UpreadAcquire == 
  IF writer = FALSE /\ upreader = FALSE
  THEN 
    upreader' = TRUE
    /\ UNCHANGED <<writer, being_upgraded, reader_count, queue>>  \* Added UNCHANGED for variables not modified
  ELSE 
    queue' = Append(queue, "upread")
    /\ UNCHANGED <<writer, upreader, being_upgraded, reader_count>>  \* Added UNCHANGED for variables not modified
ReadRelease == 
  /\ reader_count > 0
  /\ reader_count' = reader_count - 1
  /\ UNCHANGED <<writer, upreader, being_upgraded, queue>>
WriteRelease == 
  /\ writer = TRUE
  /\ writer' = FALSE
  /\ UNCHANGED <<upreader, being_upgraded, reader_count, queue>>
UpreadRelease == 
  /\ upreader = TRUE
  /\ upreader' = FALSE
  /\ UNCHANGED <<writer, being_upgraded, reader_count, queue>>
StartUpgrade == 
  /\ upreader = TRUE
  /\ being_upgraded = FALSE
  /\ being_upgraded' = TRUE
  /\ UNCHANGED <<writer, reader_count, queue>>
CompleteUpgrade == 
  /\ being_upgraded = TRUE
  /\ reader_count = 0
  /\ writer' = TRUE
  /\ being_upgraded' = FALSE
  /\ UNCHANGED <<upreader, reader_count, queue>>
Downgrade == 
  /\ writer = TRUE
  /\ writer' = FALSE
  /\ upreader' = TRUE
  /\ being_upgraded' = FALSE
  /\ UNCHANGED <<reader_count, queue>>
AcquireFromQueue == 
  IF Len(queue) > 0 
  THEN 
    LET op = Head(queue)
    IN 
      IF (op = "read" /\ writer = FALSE /\ being_upgraded = FALSE)
         \/ (op = "write" /\ writer = FALSE /\ upreader = FALSE /\ reader_count = 0 /\ being_upgraded = FALSE)
         \/ (op = "upread" /\ writer = FALSE /\ upreader = FALSE)
      THEN 
        CASE op OF
          "read" -> reader_count' = reader_count + 1
          "write" -> writer' = TRUE
          "upread" -> upreader' = TRUE
        END CASE
        /\ queue' = Tail(queue)
        /\ UNCHANGED (  \* Added UNCHANGED for variables not modified, based on op
             IF op = "read" THEN <<writer, upreader, being_upgraded>>
             ELSE IF op = "write" THEN <<upreader, being_upgraded, reader_count>>
             ELSE <<writer, being_upgraded, reader_count>>
           )
      ELSE 
        UNCHANGED <<writer, upreader, being_upgraded, reader_count, queue>>
      END IF
  ELSE 
    UNCHANGED <<writer, upreader, being_upgraded, reader_count, queue>>
  END IF
Next == 
  ReadAcquire \/ WriteAcquire \/ UpreadAcquire \/ ReadRelease \/ WriteRelease \/ UpreadRelease \/ StartUpgrade \/ CompleteUpgrade \/ Downgrade \/ AcquireFromQueue
Spec == 
  Init 
  /\ [][Next]_vars 
  /\ WF_vars(ReadRelease) 
  /\ WF_vars(WriteRelease) 
  /\ WF_vars(UpreadRelease) 
  /\ WF_vars(AcquireFromQueue)
====