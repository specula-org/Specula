---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Val, PROD, Consumers, Nil, None

ASSUME PROD \notin Consumers
ASSUME Nil \notin Val /\ None \notin Val

MsgKind == {"request","produce"}

Nodes == Consumers \cup {PROD}

Maybe(S) == S \cup {None}

Message ==
  { [kind |-> k, src |-> s, dst |-> d, val |-> v] :
      \E k \in MsgKind, s \in Nodes, d \in Nodes, v \in (Val \cup {Nil}) : TRUE }

Req(c) == [kind |-> "request", src |-> c, dst |-> PROD, val |-> Nil]
Prod(c, v) == [kind |-> "produce", src |-> PROD, dst |-> c, val |-> v]

VARIABLES pcC, pcP, net, requester, proc, s

vars == << pcC, pcP, net, requester, proc, s >>

Init ==
  /\ pcC \in [Consumers -> {"c","c1","c2"}]
  /\ pcC = [c \in Consumers |-> "c"]
  /\ pcP \in {"p","p1","p2"}
  /\ pcP = "p"
  /\ net \in [Nodes -> Seq(Message)]
  /\ net = [n \in Nodes |-> << >>]
  /\ requester \in Consumers \cup {None}
  /\ requester = None
  /\ proc \in [Consumers -> Maybe(Val)]
  /\ proc = [c \in Consumers |-> None]
  /\ s \in Val

C_c_to_c1(c) ==
  /\ c \in Consumers
  /\ pcC[c] = "c"
  /\ pcC' = [pcC EXCEPT ![c] = "c1"]
  /\ UNCHANGED << pcP, net, requester, proc, s >>

C_SendRequest(c) ==
  /\ c \in Consumers
  /\ pcC[c] = "c1"
  /\ net' = [net EXCEPT ![PROD] = Append(net[PROD], Req(c))]
  /\ pcC' = [pcC EXCEPT ![c] = "c2"]
  /\ UNCHANGED << pcP, requester, proc, s >>

C_ReceiveProduce(c) ==
  /\ c \in Consumers
  /\ pcC[c] = "c2"
  /\ net[c] /= << >>
  /\ Head(net[c]).kind = "produce"
  /\ Head(net[c]).dst = c
  /\ LET m == Head(net[c]) IN
       /\ proc' = [proc EXCEPT ![c] = m.val]
       /\ net' = [net EXCEPT ![c] = Tail(net[c])]
       /\ pcC' = [pcC EXCEPT ![c] = "c"]
       /\ UNCHANGED << pcP, requester, s >>

P_p_to_p1 ==
  /\ pcP = "p"
  /\ pcP' = "p1"
  /\ UNCHANGED << pcC, net, requester, proc, s >>

P_DequeueRequest ==
  /\ pcP = "p1"
  /\ net[PROD] /= << >>
  /\ Head(net[PROD]).kind = "request"
  /\ LET m == Head(net[PROD]) IN
       /\ requester' = m.src
       /\ net' = [net EXCEPT ![PROD] = Tail(net[PROD])]
       /\ pcP' = "p2"
       /\ UNCHANGED << pcC, proc, s >>

P_SendProduce ==
  /\ pcP = "p2"
  /\ requester \in Consumers
  /\ LET v == s IN
       /\ net' = [net EXCEPT ![requester] = Append(net[requester], Prod(requester, v))]
       /\ requester' = None
       /\ pcP' = "p"
       /\ UNCHANGED << pcC, proc, s >>

Next ==
  \/ \E c \in Consumers : C_c_to_c1(c)
  \/ \E c \in Consumers : C_SendRequest(c)
  \/ P_p_to_p1
  \/ P_DequeueRequest
  \/ P_SendProduce
  \/ \E c \in Consumers : C_ReceiveProduce(c)

Spec == Init /\ [][Next]_vars

====