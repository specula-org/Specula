---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Replicas, Commands, Keys, key
ASSUME Replicas # {} /\ Commands # {} /\ Keys # {} 
ASSUME key \in [Commands -> Keys]

N == Cardinality(Replicas)
Quorum == (N \div 2) + 1
RecoverQuorum == (Quorum \div 2) + 1
SuperQuorum == (N - Quorum) + RecoverQuorum

VARIABLES proposed, specPool, uncommittedPool, committed, leader

vars == <<proposed, specPool, uncommittedPool, committed, leader>>

Init == 
  proposed = {} 
  /\ specPool = [r \in Replicas |-> {}]
  /\ uncommittedPool = [r \in Replicas |-> {}]
  /\ committed = {}
  /\ leader \in Replicas \cup {NULL}

Propose(cmd) == 
  /\ cmd \notin proposed
  /\ proposed' = proposed \cup {cmd}
  /\ UNCHANGED <<specPool, uncommittedPool, committed, leader>>

ProcessProposeNonLeader(r, cmd) == 
  /\ r \in Replicas
  /\ leader /= r
  /\ cmd \in proposed
  /\ cmd \notin specPool[r]
  /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {cmd}]
  /\ UNCHANGED <<uncommittedPool, committed, leader, proposed>>

ProcessProposeLeader(r, cmd) == 
  /\ r \in Replicas
  /\ leader = r
  /\ cmd \in proposed
  /\ cmd \notin specPool[r]
  /\ cmd \notin uncommittedPool[r]
  /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {cmd}]
  /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = uncommittedPool[r] \cup {cmd}]
  /\ UNCHANGED <<committed, leader, proposed>>

Commit(cmd) == 
  /\ leader /= NULL
  /\ cmd \in uncommittedPool[leader]
  /\ committed' = committed \cup {cmd}
  /\ UNCHANGED <<specPool, uncommittedPool, leader, proposed>>

ProcessCommitMsg(r, cmd) == 
  /\ cmd \in committed
  /\ cmd \in specPool[r]
  /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \ {cmd}]
  /\ UNCHANGED <<uncommittedPool, committed, leader, proposed>>

LeaderChange(l) == 
  /\ l \in Replicas
  /\ leader' = l
  /\ specPool' = [specPool EXCEPT ![l] = { c \in Commands | Cardinality({ r \in Replicas | c \in specPool[r] }) >= RecoverQuorum } ]
  /\ UNCHANGED <<uncommittedPool, committed, proposed>>

Next == 
  \/ \E cmd \in Commands : Propose(cmd)
  \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
  \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
  \/ \E cmd \in Commands : Commit(cmd)
  \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
  \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars
====