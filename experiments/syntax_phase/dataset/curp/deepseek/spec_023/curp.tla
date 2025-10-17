---- MODULE curp ----
EXTENDS Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Replicas, Commands, Keys, KeyOf
VARIABLES leader, term, specPool, uncommittedPool, committed, receivedCommands
N == Cardinality(Replicas)
Quorum == N \div 2 + 1
FaultTolerance == N - Quorum
RecoverQuorum == Quorum \div 2 + 1
SuperQuorum == FaultTolerance + RecoverQuorum
KeyConflict(cmd1, cmd2) == KeyOf(cmd1) = KeyOf(cmd2)
Init == 
  /\ leader = CHOOSE l \in Replicas : TRUE
  /\ term = 0
  /\ specPool = [r \in Replicas |-> {}]
  /\ uncommittedPool = {}
  /\ committed = {}
  /\ receivedCommands = [r \in Replicas |-> {}]
Propose(cmd) == 
  /\ receivedCommands' = [r \in Replicas |-> receivedCommands[r] \cup {cmd}]
  /\ UNCHANGED <<leader, term, specPool, uncommittedPool, committed>>
ProcessProposeNonLeader(r, cmd) == 
  /\ r # leader
  /\ cmd \in receivedCommands[r]
  /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {cmd}]
  /\ receivedCommands' = [receivedCommands EXCEPT ![r] = receivedCommands[r] \ {cmd}]
  /\ UNCHANGED <<leader, term, uncommittedPool, committed>>
ProcessProposeLeader(r, cmd) == 
  /\ r = leader
  /\ cmd \in receivedCommands[r]
  /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {cmd}]
  /\ uncommittedPool' = uncommittedPool \cup {cmd}
  /\ receivedCommands' = [receivedCommands EXCEPT ![r] = receivedCommands[r] \ {cmd}]
  /\ UNCHANGED <<leader, term, committed>>
Commit == 
  \E cmd \in uncommittedPool : 
    LET havingCmd == {r \in Replicas : cmd \in specPool[r]}
    IN Cardinality(havingCmd) >= Quorum
    /\ committed' = committed \cup {cmd}
    /\ uncommittedPool' = uncommittedPool \ {cmd}
    /\ specPool' = [r \in Replicas |-> specPool[r] \ {cmd}]
    /\ UNCHANGED <<leader, term, receivedCommands>>
ProcessCommitMsg(r, cmd) == 
  /\ cmd \in committed
  /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \ {cmd}]
  /\ IF r = leader THEN uncommittedPool' = uncommittedPool \ {cmd} ELSE UNCHANGED uncommittedPool
  /\ UNCHANGED <<leader, term, receivedCommands, committed>>
LeaderChange(l) == 
  /\ l \in Replicas
  /\ leader' = l
  /\ term' = term + 1
  /\ \E Q \in {S \in SUBSET Replicas : Cardinality(S) >= RecoverQuorum} :
      LET recoveredSpec == {cmd \in Commands : \A r \in Q : cmd \in specPool[r]} \ committed
      IN specPool' = [r \in Replicas |-> (IF r = l THEN specPool[r] \cup recoveredSpec ELSE specPool[r]) \ committed]
      /\ uncommittedPool' = recoveredSpec
  /\ receivedCommands' = receivedCommands
  /\ committed' = committed
Next == 
  \/ \E cmd \in Commands : Propose(cmd)
  \/ \E r \in Replicas, cmd \in receivedCommands[r] : 
        IF r = leader THEN ProcessProposeLeader(r, cmd) ELSE ProcessProposeNonLeader(r, cmd)
  \/ Commit
  \/ \E r \in Replicas, cmd \in committed : ProcessCommitMsg(r, cmd)
  \/ \E l \in Replicas : LeaderChange(l)
Spec == Init /\ [][Next]_vars
====