----MODULE ProcessQueue ----
EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals

VARIABLES status, queue, counter
ProcessQueue == 
    /\ queue # <<>>
    /\ status' = "processing"
    /\ queue' = Tail(queue)
    /\ UNCHANGED counter
====
