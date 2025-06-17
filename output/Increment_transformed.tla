Increment ==
    /\ counter < 100
    /\ counter' = counter + 1
    /\ UNCHANGED <<status, queue>>
HandleIncrement ==
    /\ pc = Nil
    /\ Increment
    /\ UNCHANGED <<>>
