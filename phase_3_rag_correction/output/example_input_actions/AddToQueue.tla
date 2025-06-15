----MODULE AddToQueue ----
EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals
VARIABLES queue, status, counter
AddToQueue(item) == 
    /\ Len(queue) < 10
    /\ queue' = Append(queue, item)
    /\ UNCHANGED <<counter, status>>
====
