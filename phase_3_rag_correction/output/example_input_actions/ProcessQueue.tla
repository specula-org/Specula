----MODULE ProcessQueue ----
EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals
VARIABLES queue, status, counter
ProcessQueue == 
    /\ queue # <<>>
    /\ status' = "processing"
    /\ queue' = Tail(queue)
    /\ UNCHANGED counter
====
