---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NUM_CONSUMERS, DataSource

ASSUME NUM_CONSUMERS \in Nat \ {0}
ASSUME IsFiniteSeq(DataSource)

Producer == 0
Consumer == 1..NUM_CONSUMERS
Node == {Producer} \cup Consumer

vars == << pc, net, s, requester, processed >>

Init ==
    /\ pc = [n \in Node |-> IF n = Producer THEN "p" ELSE "c"]
    /\ net = [n \in Node |-> <<>>]
    /\ s = DataSource
    /\ requester \in Consumer
    /\ processed = [c \in Consumer |-> <<>>]

Consumer_c(self) ==
    /\ pc[self] = "c"
    /\ pc' = [pc EXCEPT ![self] = "c1"]
    /\ UNCHANGED <<net, s, requester, processed>>

Consumer_c1(self) ==
    /\ pc[self] = "c1"
    /\ net' = [net EXCEPT ![Producer] = Append(@, self)]
    /\ pc' = [pc EXCEPT ![self] = "c2"]
    /\ UNCHANGED <<s, requester, processed>>

Consumer_c2(self) ==
    /\ pc[self] = "c2"
    /\ Len(net[self]) > 0
    /\ LET msg == Head(net[self]) IN
        /\ net' = [net EXCEPT ![self] = Tail(@)]
        /\ processed' = [processed EXCEPT ![self] = Append(@, msg)]
    /\ pc' = [pc EXCEPT ![self] = "c"]
    /\ UNCHANGED <<s, requester>>

Producer_p ==
    /\ pc[Producer] = "p"
    /\ pc' = [pc EXCEPT ![Producer] = "p1"]
    /\ UNCHANGED <<net, s, requester, processed>>

Producer_p1 ==
    /\ pc[Producer] = "p1"
    /\ Len(net[Producer]) > 0
    /\ LET req == Head(net[Producer]) IN
        /\ net' = [net EXCEPT ![Producer] = Tail(@)]
        /\ requester' = req
    /\ pc' = [pc EXCEPT ![Producer] = "p2"]
    /\ UNCHANGED <<s, processed>>

Producer_p2 ==
    /\ pc[Producer] = "p2"
    /\ Len(s) > 0
    /\ LET data == Head(s) IN
        /\ s' = Tail(s)
        /\ net' = [net EXCEPT ![requester] = Append(@, data)]
    /\ pc' = [pc EXCEPT ![Producer] = "p"]
    /\ UNCHANGED <<requester, processed>>

Next ==
    \/ (\E self \in Consumer :
            \/ Consumer_c(self)
            \/ Consumer_c1(self)
            \/ Consumer_c2(self))
    \/ Producer_p
    \/ Producer_p1
    \/ Producer_p2

Spec == Init /\ [][Next]_vars

====