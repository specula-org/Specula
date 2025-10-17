---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Threads
VARIABLES writer, upgradeable_reader, being_upgraded, reader_count, held
vars == <<writer, upgradeable_reader, being_upgraded, reader_count, held>>
Init == 
    writer = FALSE 
    /\ upgradeable_reader = FALSE 
    /\ being_upgraded = FALSE 
    /\ reader_count = 0 
    /\ held = [t \in Threads |-> "none"]
AcquireRead(t) == 
    /\ held[t] = "none"
    /\ writer = FALSE
    /\ being_upgraded = FALSE
    /\ held' = [held EXCEPT ![t] = "read"]
    /\ reader_count' = reader_count + 1
    /\ UNCHANGED <<writer, upgradeable_reader, being_upgraded>>
AcquireWrite(t) == 
    /\ held[t] = "none"
    /\ writer = FALSE
    /\ upgradeable_reader = FALSE
    /\ reader_count = 0
    /\ being_upgraded = FALSE
    /\ held' = [held EXCEPT ![t] = "write"]
    /\ writer' = TRUE
    /\ UNCHANGED <<upgradeable_reader, being_upgraded, reader_count>>
AcquireUpread(t) == 
    /\ held[t] = "none"
    /\ writer = FALSE
    /\ upgradeable_reader = FALSE
    /\ held' = [held EXCEPT ![t] = "upread"]
    /\ upgradeable_reader' = TRUE
    /\ UNCHANGED <<writer, being_upgraded, reader_count>>
ReleaseRead(t) == 
    /\ held[t] = "read"
    /\ held' = [held EXCEPT ![t] = "none"]
    /\ reader_count' = reader_count - 1
    /\ UNCHANGED <<writer, upgradeable_reader, being_upgraded>>
ReleaseWrite(t) == 
    /\ held[t] = "write"
    /\ held' = [held EXCEPT ![t] = "none"]
    /\ writer' = FALSE
    /\ UNCHANGED <<upgradeable_reader, being_upgraded, reader_count>>
ReleaseUpread(t) == 
    /\ held[t] = "upread"
    /\ held' = [held EXCEPT ![t] = "none"]
    /\ upgradeable_reader' = FALSE
    /\ UNCHANGED <<writer, being_upgraded, reader_count>>
StartUpgrade(t) == 
    /\ held[t] = "upread"
    /\ being_upgraded = FALSE
    /\ being_upgraded' = TRUE
    /\ UNCHANGED <<writer, upgradeable_reader, reader_count, held>>
CompleteUpgrade(t) == 
    /\ held[t] = "upread"
    /\ being_upgraded = TRUE
    /\ reader_count = 0
    /\ held' = [held EXCEPT ![t] = "write"]
    /\ writer' = TRUE
    /\ upgradeable_reader' = FALSE
    /\ being_upgraded' = FALSE
    /\ UNCHANGED reader_count
Downgrade(t) == 
    /\ held[t] = "write"
    /\ held' = [held EXCEPT ![t] = "upread"]
    /\ writer' = FALSE
    /\ upgradeable_reader' = TRUE
    /\ UNCHANGED <<being_upgraded, reader_count>>
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
Fairness == 
    /\ \A t \in Threads : WF_vars(AcquireRead(t))
    /\ \A t \in Threads : WF_vars(AcquireWrite(t))
    /\ \A t \in Threads : WF_vars(AcquireUpread(t))
    /\ \A t \in Threads : WF_vars(ReleaseRead(t))
    /\ \A t \in Threads : WF_vars(ReleaseWrite(t))
    /\ \A t \in Threads : WF_vars(ReleaseUpread(t))
    /\ \A t \in Threads : WF_vars(StartUpgrade(t))
    /\ \A t \in Threads : WF_vars(CompleteUpgrade(t))
    /\ \A t \in Threads : WF_vars(Downgrade(t))
Spec == Init /\ [][Next]_vars /\ Fairness
====