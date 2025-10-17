---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NUM_CONSUMERS, PRODUCER, VALS

ASSUME PRODUCER ∉ 1..NUM_CONSUMERS
ASSUME VALS # {}

Consumers == 1..NUM_CONSUMERS
NODES == Consumers \cup {PRODUCER}
NUM_NODES == NUM_CONSUMERS + 1

Requests == { [type |-> "request", from |-> c] : c \in Consumers }
Produces == { [type |-> "produce", val |-> v] : v \in VALS }
Message == Requests \cup Produces

IsRequest(m) == m.type = "request"
IsProduce(m) == m.type = "produce"

Append(s, x) == s \o << x >>

VARIABLES pc, Net, requester, Recv

vars == << pc, Net, requester, Recv >>

Init ==
  /\ pc = [n \in NODES |-> IF n = PRODUCER THEN "p" ELSE "c"]
  /\ Net = [n \in NODES |-> << >>]
  /\ requester = "null"
  /\ Recv = [c \in Consumers |-> << >>]

C_c_to_c1(c) ==
  /\ c \in Consumers
  /\ pc[c] = "c"
  /\ pc' = [pc EXCEPT ![c] = "c1"]
  /\ UNCHANGED << Net, requester, Recv >>

C_c1_to_c2(c) ==
  /\ c \in Consumers
  /\ pc[c] = "c1"
  /\ Net' = [Net EXCEPT ![PRODUCER] = Append(@, [type |-> "request", from |-> c])]
  /\ pc' = [pc EXCEPT ![c] = "c2"]
  /\ UNCHANGED << requester, Recv >>

C_c2_to_c(c) ==
  /\ c \in Consumers
  /\ pc[c] = "c2"
  /\ Len(Net[c]) > 0
  /\ IsProduce(Head(Net[c]))
  /\ LET m == Head(Net[c]) IN
       /\ Recv' = [Recv EXCEPT ![c] = Append(@, m.val)]
       /\ Net'  = [Net  EXCEPT ![c] = Tail(@)]
  /\ pc' = [pc EXCEPT ![c] = "c"]
  /\ UNCHANGED requester

P_p_to_p1 ==
  /\ pc[PRODUCER] = "p"
  /\ pc' = [pc EXCEPT ![PRODUCER] = "p1"]
  /\ UNCHANGED << Net, requester, Recv >>

P_p1_to_p2 ==
  /\ pc[PRODUCER] = "p1"
  /\ Len(Net[PRODUCER]) > 0
  /\ IsRequest(Head(Net[PRODUCER]))
  /\ LET m == Head(Net[PRODUCER]) IN requester' = m.from
  /\ Net' = [Net EXCEPT ![PRODUCER] = Tail(@)]
  /\ pc' = [pc EXCEPT ![PRODUCER] = "p2"]
  /\ UNCHANGED Recv

P_p2_to_p ==
  /\ pc[PRODUCER] = "p2"
  /\ requester \in Consumers
  /\ \E v \in VALS:
       Net' = [Net EXCEPT ![requester] = Append(@, [type |-> "produce", val |-> v])]
  /\ pc' = [pc EXCEPT ![PRODUCER] = "p"]
  /\ UNCHANGED << requester, Recv >>

Next ==
  \/ \E c \in Consumers: C_c_to_c1(c)
  \/ \E c \in Consumers: C_c1_to_c2(c)
  \/ \E c \in Consumers: C_c2_to_c(c)
  \/ P_p_to_p1
  \/ P_p1_to_p2
  \/ P_p2_to_p

Spec == Init /\ [][Next]_vars
====