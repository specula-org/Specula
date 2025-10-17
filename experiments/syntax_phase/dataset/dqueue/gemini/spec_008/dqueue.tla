---- MODULE dqueue ----
EXTENDS Sequences, Naturals, FiniteSets, Strings

CONSTANTS PRODUCER, CONSUMERS, DataSource

ASSUME PRODUCER \notin CONSUMERS
ASSUME IsFiniteSet(CONSUMERS)
ASSUME \A i \in DOMAIN DataSource : DataSource[i] \in STRING

Nodes == CONSUMERS \cup {PRODUCER}

VARIABLES pc, net, requester, proc, s_idx

vars == <<pc, net, requester, proc, s_idx>>

Init ==
    /\ pc = [n \in Nodes |-> IF n = PRODUCER THEN "p" ELSE "c"]
    /\ net = [n \in Nodes |-> <<>>]
    /\ requester = "none"
    /\ proc = [c \in CONSUMERS |-> "none"]
    /\ s_idx = 1

C_ChooseToRequest(self) ==
    /\ pc[self] = "c"
    /\ pc' = [pc EXCEPT ![self] = "c1"]
    /\ UNCHANGED <<net, requester, proc, s_idx>>

C_SendRequest(self) ==
    /\ pc[self] = "c1"
    /\ LET msg == [type |-> "request", from |-> self]
       IN net' = [net EXCEPT ![PRODUCER] = Append(net[PRODUCER], msg)]
    /\ pc' = [pc EXCEPT ![self] = "c2"]
    /\ UNCHANGED <<requester, proc, s_idx>>

C_ReceiveData(self) ==
    /\ pc[self] = "c2"
    /\ net[self] /= <<>>
    /\ LET msg == Head(net[self]) IN
       /\ msg.type = "produce"
       /\ proc' = [proc EXCEPT ![self] = msg.data]
       /\ net' = [net EXCEPT ![self] = Tail(net[self])]
    /\ pc' = [pc EXCEPT ![self] = "c"]
    /\ UNCHANGED <<requester, s_idx>>

P_ChooseToReceive(self) ==
    /\ self = PRODUCER
    /\ pc[self] = "p"
    /\ pc' = [pc EXCEPT ![self] = "p1"]
    /\ UNCHANGED <<net, requester, proc, s_idx>>

P_ReceiveRequest(self) ==
    /\ self = PRODUCER
    /\ pc[self] = "p1"
    /\ net[self] /= <<>>
    /\ LET msg == Head(net[self]) IN
       /\ msg.type = "request"
       /\ requester' = msg.from
       /\ net' = [net EXCEPT ![self] = Tail(net[self])]
    /\ pc' = [pc EXCEPT ![self] = "p2"]
    /\ UNCHANGED <<proc, s_idx>>

P_SendData(self) ==
    /\ self = PRODUCER
    /\ pc[self] = "p2"
    /\ s_idx <= Len(DataSource)
    /\ LET data == DataSource[s_idx]
       IN LET msg == [type |-> "produce", data |-> data]
          IN net' = [net EXCEPT ![requester] = Append(net[requester], msg)]
    /\ s_idx' = s_idx + 1
    /\ pc' = [pc EXCEPT ![self] = "p"]
    /\ UNCHANGED <<requester, proc>>

Next ==
    \/ (\E self \in CONSUMERS:
        \/ C_ChooseToRequest(self)
        \/ C_SendRequest(self)
        \/ C_ReceiveData(self))
    \/ (\E self \in {PRODUCER}:
        \/ P_ChooseToReceive(self)
        \/ P_ReceiveRequest(self)
        \/ P_SendData(self))

Spec == Init /\ [][Next]_vars

====