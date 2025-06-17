ProcessQueue ==
    /\ queue # <<>>
    /\ status' = "processing"
    /\ queue' = Tail(queue)
    /\ UNCHANGED counter
HandleProcessQueue ==
    /\ pc = Nil
    /\ ProcessQueue
    /\ UNCHANGED <<>>
