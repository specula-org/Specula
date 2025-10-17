---- MODULE curp ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Replicas, Keys, ClientIds, Commands, MaxSeq
ASSUME Replicas /= {} /\ Keys /= {} /\ ClientIds /= {} /\ Commands /= {} /\ MaxSeq \in Nat /\ MaxSeq > 0

VARIABLES proposedCommands, specPool, uncommittedPool, committed, appliedIndex, leader, term, clientSeq, nextClientSeq

vars == << proposedCommands, specPool, uncommittedPool, committed, appliedIndex, leader, term, clientSeq, nextClientSeq >>

Init == 
    /\ proposedCommands = {}
    /\ specPool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ committed = [r \in Replicas |-> {}]
    /\ appliedIndex = [r \in Replicas |-> 0]
    /\ leader = [r \in Replicas |-> CHOOSE n \in Replicas : TRUE] 
    /\ term = [r \in Replicas |-> 0]
    /\ clientSeq = [r \in Replicas |-> [c \in ClientIds |-> 0]]
    /\ nextClientSeq = [c \in ClientIds |-> 1]

Propose(c, cmd) == 
    /\ nextClientSeq[c] <= MaxSeq
    /\ LET s == nextClientSeq[c]
           proposeId == <<c, s>> IN
       /\ nextClientSeq' = [nextClientSeq EXCEPT ![c] = s + 1]
       /\ proposedCommands' = proposedCommands \cup {<<proposeId, cmd>>}
       /\ \A r \in Replicas : clientSeq'[r][c] = s
       /\ UNCHANGED <<specPool, uncommittedPool, committed, appliedIndex, leader, term>>

ProcessProposeLeader(r, proposeId, cmd) == 
    /\ <<proposeId, cmd>> \in proposedCommands
    /\ leader[r] = r
    /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {<<proposeId, cmd>>}]
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = uncommittedPool[r] \cup {<<proposeId, cmd>>}]
    /\ UNCHANGED <<proposedCommands, committed, appliedIndex, leader, term, clientSeq, nextClientSeq>>

ProcessProposeNonLeader(r, proposeId, cmd) == 
    /\ <<proposeId, cmd>> \in proposedCommands
    /\ leader[r] /= r
    /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {<<proposeId, cmd>>}]
    /\ UNCHANGED <<proposedCommands, uncommittedPool, committed, appliedIndex, leader, term, clientSeq, nextClientSeq>>

Commit(proposeId, cmd) == 
    /\ \E l \in Replicas : leader[l] = l
    /\ <<proposeId, cmd>> \in uncommittedPool[l]
    /\ LET quorumSet == { r \in Replicas : <<proposeId, cmd>> \in specPool[r] } IN
       Cardinality(quorumSet) >= (Cardinality(Replicas) \div 2 + 1)
    /\ committed' = [r \in Replicas |-> committed[r] \cup {proposeId}]
    /\ specPool' = [r \in Replicas |-> { <<pid, c>> \in specPool[r] : pid /= proposeId } ]
    /\ uncommittedPool' = [r \in Replicas |-> { <<pid, c>> \in uncommittedPool[r] : pid /= proposeId } ]
    /\ appliedIndex' = [r \in Replicas |-> appliedIndex[r] + 1]
    /\ UNCHANGED <<proposedCommands, leader, term, clientSeq, nextClientSeq>>

LeaderChange(l) == 
    /\ l \in Replicas
    /\ \A r \in Replicas : leader'[r] = l
    /\ term' = [r \in Replicas |-> term[r] + 1]
    /\ LET quorumSet == CHOOSE Q \in SUBSET Replicas : Cardinality(Q) >= (Cardinality(Replicas) \div 2 + 1) IN
       /\ specPool' = [r \in Replicas |-> IF r = l THEN UNION { specPool[q] : q \in quorumSet } ELSE specPool[r] ]
       /\ uncommittedPool' = [r \in Replicas |-> IF r = l THEN UNION { uncommittedPool[q] : q \in quorumSet } ELSE uncommittedPool[r] ]
    /\ UNCHANGED <<proposedCommands, committed, appliedIndex, clientSeq, nextClientSeq>>

Next == 
    \/ \E c \in ClientIds, cmd \in Commands : Propose(c, cmd)
    \/ \E r \in Replicas, proposeId \in DOMAIN proposedCommands, cmd \in Commands : ProcessProposeLeader(r, proposeId, cmd)
    \/ \E r \in Replicas, proposeId \in DOMAIN proposedCommands, cmd \in Commands : ProcessProposeNonLeader(r, proposeId, cmd)
    \/ \E proposeId \in DOMAIN proposedCommands, cmd \in Commands : Commit(proposeId, cmd)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====