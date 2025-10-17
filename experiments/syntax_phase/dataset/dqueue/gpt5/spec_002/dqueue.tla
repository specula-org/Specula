---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NumConsumers, ItemPool

Producer == "producer"
Server == "server"
Consumers == 1..NumConsumers
Nodes == {Server} \cup {Producer} \cup Consumers

MessageType == {"request", "produce"}
NoItem == "NoItem"
Message == [type: MessageType, from: Nodes, item: ItemPool \cup {NoItem}]

VARIABLES Net, ItemsQ, WaitQ, CState, PState

ReqMsg(i) == [type |-> "request", from |-> i, item |-> NoItem]
ProdMsg(src, it) == [type |-> "produce", from |-> src, item |-> it]

TypeOK ==
    /\ Net \in [Nodes -> Seq(Message)]
    /\ ItemsQ \in Seq(ItemPool)
    /\ WaitQ \in Seq(Consumers)
    /\ CState \in [Consumers -> {"c","c1","c2"}]
    /\ PState \in {"p","p1","p2"}

Init ==
    /\ Net \in [Nodes -> Seq(Message)]
    /\ \A n \in Nodes: Net[n] = << >>
    /\ ItemsQ = << >>
    /\ WaitQ = << >>
    /\ CState \in [Consumers -> {"c","c1","c2"}]
    /\ \A i \in Consumers: CState[i] = "c"
    /\ PState \in {"p","p1","p2"}
    /\ PState = "p"

ConsumerRequest(i) ==
    /\ i \in Consumers
    /\ CState[i] = "c"
    /\ Net' = [Net EXCEPT ![Server] = Append(@, ReqMsg(i))]
    /\ CState' = [CState EXCEPT ![i] = "c1"]
    /\ UNCHANGED << ItemsQ, WaitQ, PState >>

ConsumerReceive(i) ==
    /\ i \in Consumers
    /\ CState[i] = "c1"
    /\ Net[i] # << >>
    /\ Head(Net[i]).type = "produce"
    /\ Net' = [Net EXCEPT ![i] = Tail(@)]
    /\ CState' = [CState EXCEPT ![i] = "c2"]
    /\ UNCHANGED << ItemsQ, WaitQ, PState >>

ConsumerReset(i) ==
    /\ i \in Consumers
    /\ CState[i] = "c2"
    /\ CState' = [CState EXCEPT ![i] = "c"]
    /\ UNCHANGED << Net, ItemsQ, WaitQ, PState >>

ProducerProduce ==
    /\ PState = "p"
    /\ \E it \in ItemPool:
        /\ Net' = [Net EXCEPT ![Server] = Append(@, ProdMsg(Producer, it))]
        /\ UNCHANGED << ItemsQ, WaitQ, CState >>
    /\ PState' = "p1"

ProducerAdvance1 ==
    /\ PState = "p1"
    /\ PState' = "p2"
    /\ UNCHANGED << Net, ItemsQ, WaitQ, CState >>

ProducerReset ==
    /\ PState = "p2"
    /\ PState' = "p"
    /\ UNCHANGED << Net, ItemsQ, WaitQ, CState >>

ServerOnRequest_Deliver ==
    /\ Net[Server] # << >>
    /\ Head(Net[Server]).type = "request"
    /\ ItemsQ # << >>
    /\ LET m == Head(Net[Server]) IN
       /\ Net' = [Net EXCEPT
              ![Server] = Tail(@),
              ![m.from] = Append(@, ProdMsg(Server, Head(ItemsQ)))]
       /\ ItemsQ' = Tail(ItemsQ)
       /\ WaitQ' = WaitQ
       /\ UNCHANGED << CState, PState >>

ServerOnRequest_Enqueue ==
    /\ Net[Server] # << >>
    /\ Head(Net[Server]).type = "request"
    /\ ItemsQ = << >>
    /\ LET m == Head(Net[Server]) IN
       /\ Net' = [Net EXCEPT ![Server] = Tail(@)]
       /\ WaitQ' = Append(WaitQ, m.from)
       /\ ItemsQ' = ItemsQ
       /\ UNCHANGED << CState, PState >>

ServerOnProduce_Buffer ==
    /\ Net[Server] # << >>
    /\ Head(Net[Server]).type = "produce"
    /\ WaitQ = << >>
    /\ LET m == Head(Net[Server]) IN
       /\ Net' = [Net EXCEPT ![Server] = Tail(@)]
       /\ ItemsQ' = Append(ItemsQ, m.item)
       /\ WaitQ' = WaitQ
       /\ UNCHANGED << CState, PState >>

ServerOnProduce_Deliver ==
    /\ Net[Server] # << >>
    /\ Head(Net[Server]).type = "produce"
    /\ WaitQ # << >>
    /\ LET m == Head(Net[Server]) IN
       /\ Net' = [Net EXCEPT
             ![Server] = Tail(@),
             ![Head(WaitQ)] = Append(@, ProdMsg(Server, m.item))]
       /\ WaitQ' = Tail(WaitQ)
       /\ ItemsQ' = ItemsQ
       /\ UNCHANGED << CState, PState >>

ServerMatch ==
    /\ ItemsQ # << >>
    /\ WaitQ # << >>
    /\ Net' = [Net EXCEPT ![Head(WaitQ)] = Append(@, ProdMsg(Server, Head(ItemsQ)))]
    /\ ItemsQ' = Tail(ItemsQ)
    /\ WaitQ' = Tail(WaitQ)
    /\ UNCHANGED << CState, PState >>

Next ==
    \/ \E i \in Consumers: ConsumerRequest(i)
    \/ \E i \in Consumers: ConsumerReceive(i)
    \/ \E i \in Consumers: ConsumerReset(i)
    \/ ProducerProduce
    \/ ProducerAdvance1
    \/ ProducerReset
    \/ ServerOnRequest_Deliver
    \/ ServerOnRequest_Enqueue
    \/ ServerOnProduce_Buffer
    \/ ServerOnProduce_Deliver
    \/ ServerMatch

Vars == << Net, ItemsQ, WaitQ, CState, PState >>

Spec ==
    Init /\ [][Next]_Vars

====