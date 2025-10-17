---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NUM_CONSUMERS, PRODUCER, VALUES, SVAL

CONSUMERS == 1..NUM_CONSUMERS
Nodes == CONSUMERS \cup {PRODUCER}

ASSUME PRODUCER \notin CONSUMERS
ASSUME SVAL \in VALUES

request == "request"
produce == "produce"

None == "None"

Message(t, f, v) == [type |-> t, from |-> f, val |-> v]

Head(s) == s[1]
Tail(s) == IF Len(s) = 0 THEN << >> ELSE SubSeq(s, 2, Len(s))

VARIABLES
  CState,
  PState,
  net,
  proc,
  Requester

Init ==
  /\ CState = [i \in CONSUMERS |-> "c"]
  /\ PState = "p"
  /\ net = [i \in Nodes |-> << >>]
  /\ proc = [i \in CONSUMERS |-> None]
  /\ Requester = None

Consumer_c(i) ==
  /\ i \in CONSUMERS
  /\ CState[i] = "c"
  /\ CState' = [CState EXCEPT ![i] = "c1"]
  /\ UNCHANGED <<PState, net, proc, Requester>>

Consumer_c1(i) ==
  /\ i \in CONSUMERS
  /\ CState[i] = "c1"
  /\ net' = [net EXCEPT ![PRODUCER] = Append(net[PRODUCER], Message(request, i, None))]
  /\ CState' = [CState EXCEPT ![i] = "c2"]
  /\ UNCHANGED <<PState, proc, Requester>>

Consumer_c2(i) ==
  /\ i \in CONSUMERS
  /\ CState[i] = "c2"
  /\ Len(net[i]) > 0
  /\ Head(net[i]).type = produce
  /\ CState' = [CState EXCEPT ![i] = "c"]
  /\ net' = [net EXCEPT ![i] = Tail(net[i])]
  /\ proc' = [proc EXCEPT ![i] = Head(net[i]).val]
  /\ UNCHANGED <<PState, Requester>>

Producer_p ==
  /\ PState = "p"
  /\ PState' = "p1"
  /\ UNCHANGED <<CState, net, proc, Requester>>

Producer_p1 ==
  /\ PState = "p1"
  /\ Len(net[PRODUCER]) > 0
  /\ Head(net[PRODUCER]).type = request
  /\ Requester' = Head(net[PRODUCER]).from
  /\ net' = [net EXCEPT ![PRODUCER] = Tail(net[PRODUCER])]
  /\ PState' = "p2"
  /\ UNCHANGED <<CState, proc>>

Producer_p2 ==
  /\ PState = "p2"
  /\ Requester \in CONSUMERS
  /\ net' = [net EXCEPT ![Requester] = Append(net[Requester], Message(produce, PRODUCER, SVAL))]
  /\ PState' = "p"
  /\ UNCHANGED <<CState, proc, Requester>>

Next ==
  \/ \E i \in CONSUMERS: Consumer_c(i)
  \/ \E i \in CONSUMERS: Consumer_c1(i)
  \/ \E i \in CONSUMERS: Consumer_c2(i)
  \/ Producer_p
  \/ Producer_p1
  \/ Producer_p2

vars == <<CState, PState, net, proc, Requester>>

Spec ==
  Init /\ [][Next]_vars

====