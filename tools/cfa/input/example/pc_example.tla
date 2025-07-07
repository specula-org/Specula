---- MODULE pc_example ----
VARIABLES x, y, result

Init == 
    /\ x = 0
    /\ y = 0  
    /\ result = 0

ProcessData(input) ==
    /\ x' = input + 1
    /\ y' = CalculateValue(x')  
    /\ result' = FinalStep(y')  

CalculateValue(val) ==
    /\ val * 2 + 3

FinalStep(intermediate) ==
    /\ intermediate - 1

\* 主要动作包含多个步骤和函数调用
MainAction ==
    /\ ProcessData(5)
    /\ x' = x' + result'  

Next == MainAction

Spec == Init /\ [][Next]_<<x, y, result>>

====