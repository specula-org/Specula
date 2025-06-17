AddToQueue(item) ==
    /\ Len(queue) < 10
    /\ queue' = Append(queue, item)
    /\ UNCHANGED <<counter, status>>
HandleAddToQueue(item) ==
    /\ pc = Nil
    /\ AddToQueue(item)
    /\ UNCHANGED <<>>
