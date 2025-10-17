---- MODULE etcdraft ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS NumConsumers, Data

ASSUME NumConsumers \in Nat \ {0}
ASSUME Data # {}

P == 0
Consumers == 1..NumConsumers
Nodes == {P} \cup Consumers
Edges == Nodes \X Nodes

Null == [null |-> TRUE]
ASSUME Null \notin Data

MsgType == {"request", "produce"}

RequestMsg(from, to) ==
  [ type |-> "request",
    from |-> from,
    to   |-> to,
    item |-> Null ]

ProduceMsg(from, to, val) ==
  [ type |-> "produce",
    from |-> from,
    to   |-> to,
    item |-> val ]

PushBack(s, x) == Append(s, x)
PushFront(s, x) == <<x>> \o s
PopFront(s) == IF Len(s) = 0 THEN << >> ELSE Tail(s)
PopBack(s) == IF Len(s) = 0 THEN << >> ELSE SubSeq(s, 1, Len(s) - 1)

VARIABLES
  state,    \* [Nodes -> {"c","c1","c2","p","p1","p2"}]
  Net,      \* [Edges -> Seq([type : MsgType, from : Nodes, to : Nodes, item : Data \cup {Null}])]
  deq,      \* Seq(Data)
  pend,     \* Consumers \cup {Null}
  consumed  \* [Consumers -> Seq(Data)]

vars == << state, Net, deq, pend, consumed >>

Init ==
  /\ state = [n \in Nodes |-> IF n = P THEN "p" ELSE "c"]
  /\ Net = [e \in Edges |-> << >>]
  /\ deq = << >>
  /\ pend = Null
  /\ consumed = [n \in Consumers |-> << >>]

C_SendRequest(n) ==
  /\ n \in Consumers
  /\ state[n] = "c"
  /\ state' = [state EXCEPT ![n] = "c1"]
  /\ Net' = [Net EXCEPT ![<<n, P>>] = Append(@, RequestMsg(n, P))]
  /\ UNCHANGED <<deq, pend, consumed>>

P_RecvRequest ==
  /\ state[P] = "p"
  /\ \E c \in Consumers :
        /\ Len(Net[<<c, P>>]) > 0
        /\ Head(Net[<<c, P>>]).type = "request"
        /\ state' = [state EXCEPT ![P] = "p1"]
        /\ Net' = [Net EXCEPT ![<<c, P>>] = Tail(@)]
        /\ pend' = c
        /\ UNCHANGED <<deq, consumed>>

P_ProduceItem ==
  /\ state[P] = "p1"
  /\ \E v \in Data :
        /\ deq' = PushBack(deq, v)
        /\ state' = [state EXCEPT ![P] = "p2"]
        /\ UNCHANGED <<Net, pend, consumed>>

P_SendProduce ==
  /\ state[P] = "p2"
  /\ pend \in Consumers
  /\ deq # << >>
  /\ Net' = [Net EXCEPT ![<<P, pend>>] = Append(@, ProduceMsg(P, pend, Head(deq)))]
  /\ deq' = PopFront(deq)
  /\ state' = [state EXCEPT ![P] = "p"]
  /\ pend' = Null
  /\ UNCHANGED consumed

C_RecvProduce(n) ==
  /\ n \in Consumers
  /\ state[n] = "c1"
  /\ Len(Net[<<P, n>>]) > 0
  /\ Head(Net[<<P, n>>]).type = "produce"
  /\ LET m == Head(Net[<<P, n>>]) IN
       /\ Net' = [Net EXCEPT ![<<P, n>>] = Tail(@)]
       /\ consumed' = [consumed EXCEPT ![n] = Append(@, m.item)]
       /\ state' = [state EXCEPT ![n] = "c2"]
       /\ UNCHANGED <<deq, pend>>

C_Reset(n) ==
  /\ n \in Consumers
  /\ state[n] = "c2"
  /\ state' = [state EXCEPT ![n] = "c"]
  /\ UNCHANGED <<Net, deq, pend, consumed>>

Next ==
  \/ \E n \in Consumers : C_SendRequest(n)
  \/ P_RecvRequest
  \/ P_ProduceItem
  \/ P_SendProduce
  \/ \E n \in Consumers : C_RecvProduce(n)
  \/ \E n \in Consumers : C_Reset(n)

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  /\ state \in [Nodes -> {"c","c1","c2","p","p1","p2"}]
  /\ Net \in [Edges -> Seq([type : MsgType, from : Nodes, to : Nodes, item : Data \cup {Null}])]
  /\ deq \in Seq(Data)
  /\ pend \in Consumers \cup {Null}
  /\ consumed \in [Consumers -> Seq(Data)]

====
