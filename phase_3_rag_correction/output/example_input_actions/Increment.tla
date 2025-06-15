----MODULE Increment ----
EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals
VARIABLES status, queue, counter
Increment == 
    /\ counter < 100
    /\ counter' = counter + 1
    /\ UNCHANGED <<status, queue>>
====
