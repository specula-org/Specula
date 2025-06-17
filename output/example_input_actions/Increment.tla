----MODULE Increment ----
EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals

VARIABLES status, counter, queue
Increment == 
    /\ counter < 100
    /\ counter' = counter + 1
    /\ UNCHANGED <<status, queue>>
====
