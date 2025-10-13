---- MODULE simple ----
EXTENDS Naturals

CONSTANT MaxValue

VARIABLE counter

Init == counter = 0

Increment ==
    /\ counter < MaxValue
    /\ counter' = counter + 1

Next == Increment

Spec == Init /\ [][Next]_counter

TypeInvariant == counter \in 0..MaxValue

====
