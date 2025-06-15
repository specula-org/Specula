----------------------------- MODULE SimpleStaticAnalysisTest -----------------------------
EXTENDS Integers

VARIABLES
    x,
    y,
    z,
    pc,
    info,
    stack

vars == <<x, y, z, pc, stack, info>>

Add_y(x) ==
    /\ y' = x + y


SubAction(m) ==
    /\ LET temp1 == m + 1  
           temp2 == y - temp
    IN         
        /\ x' = x + temp1 
        /\ Add_y(x)
        /\ UNCHANGED z

Action_Call_SubAction ==
    /\ LET temp == z * 3
    IN
        /\ z' = temp
        /\ SubAction(temp)       
        /\ z' = temp
    /\ UNCHANGED <<x, y>>


=============================================================================