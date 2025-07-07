---- MODULE ud_example ----
VARIABLES counter, buffer, index

Init == 
    /\ counter = 0
    /\ buffer = <<>>
    /\ index = 1

UpdateSequence ==
    /\ counter' = counter + 1
    /\ buffer' = Append(buffer, counter) 
    /\ index' = Len(buffer) + 1         

ChainedUpdates ==
    /\ index' = index + 2
    /\ counter' = counter + index'        
    /\ buffer' = [i \in 1..counter |-> i]   

ConditionalCheck ==
    /\ counter' = counter + 5
    /\ IF counter > 10                   
       THEN /\ buffer' = <<counter>>
            /\ index' = counter - 5
       ELSE /\ buffer' = <<>>
            /\ index' = 0

Next == UpdateSequence \/ ChainedUpdates \/ ConditionalCheck

Spec == Init /\ [][Next]_<<counter, buffer, index>>

====
