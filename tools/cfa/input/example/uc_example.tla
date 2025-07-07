---- MODULE uc_example ----
VARIABLES x, y, z, status

Init == 
    /\ x = 0
    /\ y = 0
    /\ z = 0
    /\ status = "ready"

ComplexBranching ==
    /\ IF x > 5
       THEN /\ y' = y + 1
            /\ status' = "processing"
       ELSE IF y > 3
            THEN /\ z' = z * 2
                 /\ status' = "active" 
            ELSE /\ x' = x + 1

\* 另一个分支场景
ConditionalUpdate ==
    /\ IF status = "ready"
       THEN x' = x + 10
       ELSE y' = y - 1

Next == ComplexBranching \/ ConditionalUpdate

Spec == Init /\ [][Next]_<<x, y, z, status>>

====
