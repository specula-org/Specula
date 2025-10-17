---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals

CONSTANT NumConsumers

Producer == 0
Consumers == 1..NumConsumers
Nodes == {Producer} \cup Consumers

CStates == {"c", "c1", "c2"}
PStates == {"p", "p1", "p2"}

RequestMsg(c) == [type |-> "request", from |-> c]
ProduceMsg(c, i) == [type |-> "produce", to |-> c, item |-> i]

RequestMsgSet == [type: {"request"}, from: Consumers]
ProduceMsgSet == [type: {"produce"}, to: Consumers, item: Nat]
Msg == RequestMsgSet \cup ProduceMsgSet

VARIABLES network, q, cstate, pstate, items

Init ==
  /\ network \in [Nodes -> Seq(Msg)]
  /\ \A n \in Nodes: network[n] = << >>
  /\ q \in Seq(Consumers)
  /\ q = << >>
  /\ cstate \in [Consumers -> CStates]
  /\ \A c \in Consumers: cstate[c] = "c"
  /\ pstate \in PStates
  /\ pstate = "p"
  /\ items \in Nat
  /\ items = 0

CRequest(c) ==
  /\ c \in Consumers
  /\ cstate[c] = "c"
  /\ network' = [network EXCEPT ![Producer] = Append(@, RequestMsg(c))]
  /\ cstate' = [cstate EXCEPT ![c] = "c1"]
  /\ UNCHANGED << q, pstate, items >>

PRecv ==
  /\ pstate = "p"
  /\ network[Producer] # << >>
  /\ Head(network[Producer]).type = "request"
  /\ LET m == Head(network[Producer]) IN
     /\ q' = Append(q, m.from)
     /\ network' = [network EXCEPT ![Producer] = Tail(@)]
  /\ UNCHANGED << cstate, pstate, items >>

PStartProduce ==
  /\ pstate = "p"
  /\ q # << >>
  /\ pstate' = "p1"
  /\ UNCHANGED << network, q, cstate, items >>

PSendProduce ==
  /\ pstate = "p1"
  /\ q # << >>
  /\ LET c == Head(q) IN
     /\ network' = [network EXCEPT ![c] = Append(@, ProduceMsg(c, items))]
  /\ pstate' = "p2"
  /\ items' = items + 1
  /\ UNCHANGED << q, cstate >>

PFinish ==
  /\ pstate = "p2"
  /\ q # << >>
  /\ q' = Tail(q)
  /\ pstate' = "p"
  /\ UNCHANGED << network, cstate, items >>

CRecvProduce(c) ==
  /\ c \in Consumers
  /\ cstate[c] = "c1"
  /\ network[c] # << >>
  /\ Head(network[c]).type = "produce"
  /\ network' = [network EXCEPT ![c] = Tail(@)]
  /\ cstate' = [cstate EXCEPT ![c] = "c2"]
  /\ UNCHANGED << q, pstate, items >>

CReset(c) ==
  /\ c \in Consumers
  /\ cstate[c] = "c2"
  /\ cstate' = [cstate EXCEPT ![c] = "c"]
  /\ UNCHANGED << network, q, pstate, items >>

Next ==
  \/ (\E c \in Consumers: CRequest(c))
  \/ PRecv
  \/ PStartProduce
  \/ PSendProduce
  \/ PFinish
  \/ (\E c \in Consumers: CRecvProduce(c))
  \/ (\E c \in Consumers: CReset(c))

Vars == << network, q, cstate, pstate, items >>

Spec ==
  Init /\ [][Next]_Vars

TypeOK ==
  /\ network \in [Nodes -> Seq(Msg)]
  /\ q \in Seq(Consumers)
  /\ cstate \in [Consumers -> CStates]
  /\ pstate \in PStates
  /\ items \in Nat
  /\ \A i \in 1..Len(network[Producer]): network[Producer][i] \in RequestMsgSet
  /\ \A c \in Consumers:
       \A i \in 1..Len(network[c]):
         /\ network[c][i] \in ProduceMsgSet
         /\ network[c][i].to = c

====