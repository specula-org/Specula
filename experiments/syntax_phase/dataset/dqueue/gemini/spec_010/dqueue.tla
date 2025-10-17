---- MODULE dqueue ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS NUM_CONSUMERS, PRODUCER, DataSource

ASSUME NUM_CONSUMERS \in Nat \ {0}
ASSUME PRODUCER \notin (1..NUM_CONSUMERS)
ASSUME IsASequence(DataSource)

CONSUMERS == 1..NUM_CONSUMERS
NODES == CONSUMERS \cup {PRODUCER}

VARIABLES pc, net, s, proc, requester

vars == <<pc, net, s, proc, requester>>

Init ==
    /\ pc = [n \in NODES |-> IF n = PRODUCER THEN "p" ELSE "c"]
    /\ net = [n \in NODES |-> <<>>]
    /\ s = DataSource
    /\ proc = [c \in CONSUMERS |-> <<>>]
    /\ requester = [p \in {PRODUCER} |-> 0]

(* Consumer Actions *)

ConsumerRequest(self) ==
    /\ pc[self] = "c"
    /\ pc' = [pc EXCEPT ![self] = "c1"]
    /\ UNCHANGED <<net, s, proc, requester>>

ConsumerSendRequest(self) ==
    /\ pc[self] = "c1"
    /\ LET msg == [type |-> "request", from |-> self] IN
       net' = [net EXCEPT ![PRODUCER] = Append(net[PRODUCER], msg)]
    /\ pc' = [pc EXCEPT ![self] = "c2"]
    /\ UNCHANGED <<s, proc, requester>>

ConsumerReceive(self) ==
    /\ pc[self] = "c2"
    /\ Len(net[self]) > 0
    /\ LET msg == Head(net[self]) IN
       /\ msg.type = "produce"
       /\ proc' = [proc EXCEPT ![self] = Append(proc[self], msg.data)]
       /\ net' = [net EXCEPT ![self] = Tail(net[self])]
    /\ pc' = [pc EXCEPT ![self] = "c"]
    /\ UNCHANGED <<s, requester>>

AConsumer(self) ==
    \/ ConsumerRequest(self)
    \/ ConsumerSendRequest(self)
    \/ ConsumerReceive(self)

(* Producer Actions *)

ProducerAwait(self) ==
    /\ self = PRODUCER
    /\ pc[self] = "p"
    /\ pc' = [pc EXCEPT ![self] = "p1"]
    /\ UNCHANGED <<net, s, proc, requester>>

ProducerReceiveRequest(self) ==
    /\ self = PRODUCER
    /\ pc[self] = "p1"
    /\ Len(net[self]) > 0
    /\ LET msg == Head(net[self]) IN
       /\ msg.type = "request"
       /\ requester' = [requester EXCEPT ![self] = msg.from]
       /\ net' = [net EXCEPT ![self] = Tail(net[self])]
    /\ pc' = [pc EXCEPT ![self] = "p2"]
    /\ UNCHANGED <<s, proc>>

ProducerSend(self) ==
    /\ self = PRODUCER
    /\ pc[self] = "p2"
    /\ Len(s) > 0
    /\ requester[self] \in CONSUMERS
    /\ LET dest == requester[self]
           data == Head(s)
           msg == [type |-> "produce", data |-> data] IN
       /\ s' = Tail(s)
       /\ net' = [net EXCEPT ![dest] = Append(net[dest], msg)]
    /\ pc' = [pc EXCEPT ![self] = "p"]
    /\ UNCHANGED <<proc, requester>>

AProducer(self) ==
    \/ ProducerAwait(self)
    \/ ProducerReceiveRequest(self)
    \/ ProducerSend(self)

Next ==
    \/ (\E self \in CONSUMERS : AConsumer(self))
    \/ (LET self == PRODUCER IN AProducer(self))

Spec == Init /\ [][Next]_vars

====