---- MODULE dqueue ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    NUM_CONSUMERS,
    DataSource

ASSUME NUM_CONSUMERS \in Nat \ {0}
ASSUME IsASeq(DataSource)

PRODUCER == 0
Consumer == 1..NUM_CONSUMERS
Node == {PRODUCER} \cup Consumer

Nil == CHOOSE v : v = v

VARIABLES pc, net, s_idx, requester, proc

vars == <<pc, net, s_idx, requester, proc>>

Init ==
    /\ pc = [n \in Node |-> IF n = PRODUCER THEN "p" ELSE "c"]
    /\ net = [n \in Node |-> <<>>]
    /\ s_idx = 1
    /\ requester = Nil
    /\ proc = [c \in Consumer |-> Nil]

C_GotoC1(i) ==
    /\ i \in Consumer
    /\ pc[i] = "c"
    /\ pc' = [pc EXCEPT ![i] = "c1"]
    /\ UNCHANGED <<net, s_idx, requester, proc>>

C_SendRequest(i) ==
    /\ i \in Consumer
    /\ pc[i] = "c1"
    /\ pc' = [pc EXCEPT ![i] = "c2"]
    /\ net' = [net EXCEPT ![PRODUCER] = Append(net[PRODUCER], i)]
    /\ UNCHANGED <<s_idx, requester, proc>>

C_Receive(i) ==
    /\ i \in Consumer
    /\ pc[i] = "c2"
    /\ net[i] /= <<>>
    /\ pc' = [pc EXCEPT ![i] = "c"]
    /\ proc' = [proc EXCEPT ![i] = Head(net[i])]
    /\ net' = [net EXCEPT ![i] = Tail(net[i])]
    /\ UNCHANGED <<s_idx, requester>>

P_GotoP1 ==
    /\ pc[PRODUCER] = "p"
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p1"]
    /\ UNCHANGED <<net, s_idx, requester, proc>>

P_ReceiveRequest ==
    /\ pc[PRODUCER] = "p1"
    /\ net[PRODUCER] /= <<>>
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p2"]
    /\ requester' = Head(net[PRODUCER])
    /\ net' = [net EXCEPT ![PRODUCER] = Tail(net[PRODUCER])]
    /\ UNCHANGED <<s_idx, proc>>

P_Send ==
    /\ pc[PRODUCER] = "p2"
    /\ s_idx <= Len(DataSource)
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p"]
    /\ net' = [net EXCEPT ![requester] = Append(net[requester], DataSource[s_idx])]
    /\ s_idx' = s_idx + 1
    /\ UNCHANGED <<requester, proc>>

Next ==
    \/ \E i \in Consumer : C_GotoC1(i)
    \/ \E i \in Consumer : C_SendRequest(i)
    \/ \E i \in Consumer : C_Receive(i)
    \/ P_GotoP1
    \/ P_ReceiveRequest
    \/ P_Send

Spec == Init /\ [][Next]_vars

====