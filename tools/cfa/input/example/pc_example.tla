---- MODULE pc_example ----
VARIABLES x, y, result

Init == 
    /\ x = 0
    /\ y = 0  
    /\ result = 0

ProcessData(input) ==
    /\ x' = input + 1
    /\ y' = x' * 2 + 3
    /\ result' = y' + x'

MainAction ==
    /\ ProcessData(5)
    /\ x' = x' + result'  

Next == MainAction

Spec == Init /\ [][Next]_<<x, y, result>>

====