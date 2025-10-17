---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Consumers

Server == "server"
Producer == "producer"
Nodes == {Server, Producer} \cup Consumers

request == "request"
produce == "produce"

ItemSet == Nat

PushLeft(q, x) == <<x>> \o q
PushRight(q, x) == Append(q, x)
PopLeft(q) == Tail(q)
PopRight(q) == SubSeq(q, 1, Len(q) - 1)
PeekLeft(q) == Head(q)
PeekRight(q) == q[Len(q)]

ReqMsg == [type: {request}, from: Consumers]
ProdMsg == [type: {produce}, from: {Producer}, val: ItemSet]
DelMsg == [type: {produce}, from: {Server}, val: ItemSet]
Msg == ReqMsg \cup ProdMsg \cup DelMsg

VARIABLES
    net,
    deq,
    waitQ,
    nextItem,
    CState,
    PState,
    CurrC,
    stage

Init ==
    /\ CurrC \in Consumers
    /\ net = [n \in Nodes |-> << >>]
    /\ deq = << >>
    /\ waitQ = << >>
    /\ nextItem = 0
    /\ CState = [c \in Consumers |-> "c"]
    /\ PState = "p"
    /\ stage = "c"

C_to_c1 ==
    /\ stage = "c"
    /\ CState[CurrC] = "c"
    /\ net' = [net EXCEPT ![Server] = Append(@, [type |-> request, from |-> CurrC])]
    /\ CState' = [CState EXCEPT ![CurrC] = "c1"]
    /\ stage' = "c1"
    /\ UNCHANGED << deq, waitQ, nextItem, PState, CurrC >>

Server_enq_req ==
    /\ stage = "c1"
    /\ Len(net[Server]) > 0
    /\ Head(net[Server]).type = request
    /\ LET msg == Head(net[Server]) IN
       /\ waitQ' = Append(waitQ, msg.from)
       /\ net' = [net EXCEPT ![Server] = Tail(@)]
       /\ stage' = "p"
       /\ UNCHANGED << deq, nextItem, PState, CState, CurrC >>

P_to_p1 ==
    /\ stage = "p"
    /\ PState = "p"
    /\ net' = [net EXCEPT ![Server] = Append(@, [type |-> produce, from |-> Producer, val |-> nextItem])]
    /\ nextItem' = nextItem + 1
    /\ PState' = "p1"
    /\ stage' = "p1"
    /\ UNCHANGED << deq, waitQ, CState, CurrC >>

Server_handle_prod ==
    /\ stage = "p1"
    /\ Len(net[Server]) > 0
    /\ Head(net[Server]).type = produce
    /\ LET msg == Head(net[Server]) IN
       /\ deq' = PushRight(deq, msg.val)
       /\ net' = [net EXCEPT ![Server] = Tail(@)]
       /\ PState' = "p2"
       /\ stage' = "p2"
       /\ UNCHANGED << waitQ, CState, nextItem, CurrC >>

Server_deliver ==
    /\ stage = "p2"
    /\ Len(deq) > 0
    /\ Len(waitQ) > 0
    /\ LET c == Head(waitQ) IN
       /\ net' = [net EXCEPT ![c] = Append(@, [type |-> produce, from |-> Server, val |-> Head(deq)])]
       /\ deq' = PopLeft(deq)
       /\ waitQ' = Tail(waitQ)
       /\ stage' = "c2"
       /\ UNCHANGED << CState, PState, nextItem, CurrC >>

Consumer_receive ==
    /\ stage = "c2"
    /\ Len(net[CurrC]) > 0
    /\ Head(net[CurrC]).type = produce
    /\ net' = [net EXCEPT ![CurrC] = Tail(@)]
    /\ CState' = [CState EXCEPT ![CurrC] = "c2"]
    /\ stage' = "c2"
    /\ UNCHANGED << deq, waitQ, nextItem, PState, CurrC >>

C2_to_c ==
    /\ stage = "c2"
    /\ CState[CurrC] = "c2"
    /\ CState' = [CState EXCEPT ![CurrC] = "c"]
    /\ PState' = "p"
    /\ stage' = "c"
    /\ UNCHANGED << net, deq, waitQ, nextItem, CurrC >>

Next ==
    \/ C_to_c1
    \/ Server_enq_req
    \/ P_to_p1
    \/ Server_handle_prod
    \/ Server_deliver
    \/ Consumer_receive
    \/ C2_to_c

vars == << net, deq, waitQ, nextItem, CState, PState, CurrC, stage >>

Spec ==
    Init /\ [][Next]_vars

TypeOK ==
    /\ net \in [Nodes -> Seq(Msg)]
    /\ deq \in Seq(ItemSet)
    /\ waitQ \in Seq(Consumers)
    /\ nextItem \in Nat
    /\ CState \in [Consumers -> {"c", "c1", "c2"}]
    /\ PState \in {"p", "p1", "p2"}
    /\ CurrC \in Consumers
    /\ stage \in {"c", "c1", "p", "p1", "p2", "c2"}
====