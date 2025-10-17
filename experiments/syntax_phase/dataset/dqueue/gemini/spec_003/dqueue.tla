---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NUM_CONSUMERS, Data

ASSUME NUM_CONSUMERS \in Nat \ {0}
ASSUME IsFiniteSet(Data) /\ Cardinality(Data) > 0

PRODUCER == 0
Consumers == 1..NUM_CONSUMERS
Nodes == {PRODUCER} \cup Consumers

Nil == CHOOSE v : v \notin (Nodes \cup Data)

VARIABLES pc, net, s, proc, requester

vars == <<pc, net, s, proc, requester>>

Init ==
    /\ pc = [n \in Nodes |-> IF n = PRODUCER THEN "p" ELSE "c"]
    /\ net = [n \in Nodes |-> <<>>]
    /\ s = << d : d \in Data >>
    /\ proc = [c \in Consumers |-> Nil]
    /\ requester = Nil

Consumer_c(i) ==
    /\ i \in Consumers
    /\ pc[i] = "c"
    /\ pc' = [pc EXCEPT ![i] = "c1"]
    /\ UNCHANGED <<net, s, proc, requester>>

Consumer_c1(i) ==
    /\ i \in Consumers
    /\ pc[i] = "c1"
    /\ net' = [net EXCEPT ![PRODUCER] = Append(net[PRODUCER], i)]
    /\ pc' = [pc EXCEPT ![i] = "c2"]
    /\ UNCHANGED <<s, proc, requester>>

Consumer_c2(i) ==
    /\ i \in Consumers
    /\ pc[i] = "c2"
    /\ Len(net[i]) > 0
    /\ LET msg == Head(net[i]) IN
        /\ proc' = [proc EXCEPT ![i] = msg]
        /\ net' = [net EXCEPT ![i] = Tail(net[i])]
    /\ pc' = [pc EXCEPT ![i] = "c"]
    /\ UNCHANGED <<s, requester>>

Producer_p ==
    /\ pc[PRODUCER] = "p"
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p1"]
    /\ UNCHANGED <<net, s, proc, requester>>

Producer_p1 ==
    /\ pc[PRODUCER] = "p1"
    /\ Len(net[PRODUCER]) > 0
    /\ LET req == Head(net[PRODUCER]) IN
        /\ requester' = req
        /\ net' = [net EXCEPT ![PRODUCER] = Tail(net[PRODUCER])]
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p2"]
    /\ UNCHANGED <<s, proc>>

Producer_p2 ==
    /\ pc[PRODUCER] = "p2"
    /\ Len(s) > 0
    /\ LET dataToSend == Head(s)
           reqId == requester IN
        /\ net' = [net EXCEPT ![reqId] = Append(net[reqId], dataToSend)]
        /\ s' = Tail(s)
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p"]
    /\ UNCHANGED <<proc, requester>>

Next ==
    \/ \E i \in Consumers :
        \/ Consumer_c(i)
        \/ Consumer_c1(i)
        \/ Consumer_c2(i)
    \/ Producer_p
    \/ Producer_p1
    \/ Producer_p2

Spec == Init /\ [][Next]_vars

====