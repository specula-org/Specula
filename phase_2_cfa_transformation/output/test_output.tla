Add_y(x) ==
    /\ y' = x + y
SubAction(m) ==
    /\ LET temp1 == m + 1  
        temp2 == y - temp IN
        /\ x' = x + temp1
        /\ Add_y(x')
        /\ UNCHANGED z
Action_Call_SubAction_1_2 ==
        /\ z' = info.temp.temp
    /\ UNCHANGED <<x, y>>
    /\ pc' = stack.backsite
    /\ stack' = Head(stack)
    /\ info' = stack.info
Action_Call_SubAction_1 ==
        /\ SubAction(info.temp.temp)
        /\ pc' = "Action_Call_SubAction_1_2"
        /\ info' = info
Action_Call_SubAction ==
    /\ LET temp == z * 3 IN
        /\ z' = temp
        /\ pc' = "Action_Call_SubAction_1"
        /\ info' = [args |-> <<>>, temp |-> [temp |-> temp]]
HandleAction_Call_SubAction_1_2 ==
    /\ pc = "Action_Call_SubAction_1_2"
    /\ Action_Call_SubAction_1_2
    /\ UNCHANGED <<>>
HandleAction_Call_SubAction_1 ==
    /\ pc = "Action_Call_SubAction_1"
    /\ Action_Call_SubAction_1
    /\ UNCHANGED <<stack>>
HandleAction_Call_SubAction ==
    /\ pc = Nil
    /\ Action_Call_SubAction
    /\ UNCHANGED <<stack, x, y>>
