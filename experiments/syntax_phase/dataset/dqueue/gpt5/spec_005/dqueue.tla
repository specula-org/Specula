---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumConsumers, ItemVals

Producer == 0
Consumers == 1..NumConsumers
Node == {Producer} \cup Consumers

MsgType == {"request", "produce"}
NoNode == "noNode"
NoItem == "noItem"

Message == [type: MsgType, from: Node, item: ItemVals \cup {NoItem}]

PushFront(q, x) == <<x>> \o q
PushBack(q, x) == Append(q, x)
Front(q) == Head(q)
Back(q) == q[Len(q)]
PopFront(q) == Tail(q)
PopBack(q) == SubSeq(q, 1, Len(q) - 1)

VARIABLES
  pc,
  Net,
  DQ,
  prodItem,
  lastReqFrom

Init ==
  /\ pc = [n \in Node |-> IF n = Producer THEN "p" ELSE "c"]
  /\ Net = [n \in Node |-> << >>]
  /\ DQ = << >>
  /\ prodItem = NoItem
  /\ lastReqFrom = NoNode

ConsumerRequest(i) ==
  /\ i \in Consumers
  /\ pc[i] = "c"
  /\ Net' = [Net EXCEPT ![Producer] = Append(@, [type |-> "request", from |-> i, item |-> NoItem])]
  /\ pc' = [pc EXCEPT ![i] = "c1"]
  /\ UNCHANGED << DQ, prodItem, lastReqFrom >>

ProducerStart ==
  /\ pc[Producer] = "p"
  /\ Net[Producer] # << >>
  /\ Head(Net[Producer]).type = "request"
  /\ LET m == Head(Net[Producer]) IN
       /\ Net' = [Net EXCEPT ![Producer] = Tail(@)]
       /\ lastReqFrom' = m.from
       /\ prodItem' \in ItemVals
       /\ pc' = [pc EXCEPT ![Producer] = "p1"]
       /\ DQ' = DQ

ProducerProduce ==
  /\ pc[Producer] = "p1"
  /\ lastReqFrom # NoNode
  /\ Net' = [Net EXCEPT ![lastReqFrom] = Append(@, [type |-> "produce", from |-> Producer, item |-> prodItem])]
  /\ DQ' = PushBack(DQ, prodItem)
  /\ pc' = [pc EXCEPT ![Producer] = "p2"]
  /\ UNCHANGED << lastReqFrom, prodItem >>

ProducerFinish ==
  /\ pc[Producer] = "p2"
  /\ pc' = [pc EXCEPT ![Producer] = "p"]
  /\ lastReqFrom' = NoNode
  /\ prodItem' = NoItem
  /\ UNCHANGED << Net, DQ >>

ConsumerConsume(i) ==
  /\ i \in Consumers
  /\ pc[i] = "c1"
  /\ Net[i] # << >>
  /\ Head(Net[i]).type = "produce"
  /\ DQ # << >>
  /\ Net' = [Net EXCEPT ![i] = Tail(@)]
  /\ DQ' = PopFront(DQ)
  /\ pc' = [pc EXCEPT ![i] = "c2"]
  /\ UNCHANGED << lastReqFrom, prodItem >>

ConsumerReturn(i) ==
  /\ i \in Consumers
  /\ pc[i] = "c2"
  /\ pc' = [pc EXCEPT ![i] = "c"]
  /\ UNCHANGED << Net, DQ, lastReqFrom, prodItem >>

Next ==
  \E i \in Consumers:
    ConsumerRequest(i)
  \/ ProducerStart
  \/ ProducerProduce
  \/ ProducerFinish
  \/ ConsumerConsume(i)
  \/ ConsumerReturn(i)

vars == << pc, Net, DQ, prodItem, lastReqFrom >>

Spec ==
  Init /\ [][Next]_vars
====