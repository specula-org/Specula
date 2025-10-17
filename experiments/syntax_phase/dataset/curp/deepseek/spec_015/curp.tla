---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Replicas, Keys, Values, Commands
ASSUME Replicas # {} /\ Keys # {} /\ Values # {} /\ Commands \subseteq (Keys \times Values)
Key(c) == c[1]
VARIABLES leader, specPool, uncommittedPool, committed, term, proposedCommands

vars == <<leader, specPool, uncommittedPool, committed, term, proposedCommands>>

Init == 
  leader \in Replicas
  /\ specPool = [r \in Replicas |-> {}]
  /\ uncommittedPool = {}
  /\ committed = {}
  /\ term = 1
  /\ proposedCommands = {}

QuorumSize == (Cardinality(Replicas) \div 2) + 1
RecoverQuorumSize == (QuorumSize \div 2) + 1

Propose(cmd) == 
  /\ cmd \notin proposedCommands
  /\ proposedCommands' = proposedCommands \cup {cmd}
  /\ UNCHANGED <<leader, specPool, uncommittedPool, committed, term>>

ProcessProposeLeader(r, cmd) == 
  /\ cmd \in proposedCommands
  /\ r = leader
  /\ LET key == Key(cmd)
     IN IF \neg (\E c \in specPool[r] : Key(c) = key) /\ \neg (\E c \in uncommittedPool : Key(c) = key)
        THEN /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {cmd}]
             /\ uncommittedPool' = uncommittedPool \cup {cmd}
        ELSE /\ UNCHANGED <<specPool, uncommittedPool>>
  /\ UNCHANGED <<leader, committed, term, proposedCommands>>

ProcessProposeNonLeader(r, cmd) == 
  /\ cmd \in proposedCommands
  /\ r # leader
  /\ LET key == Key(cmd)
     IN IF \neg (\E c \in specPool[r] : Key(c) = key)
        THEN specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {cmd}]
        ELSE UNCHANGED specPool
  /\ UNCHANGED <<leader, uncommittedPool, committed, term, proposedCommands>>

Commit(cmd) == 
  /\ cmd \in uncommittedPool
  /\ committed' = committed \cup {cmd}
  /\ uncommittedPool' = uncommittedPool \ {cmd}
  /\ UNCHANGED <<specPool, leader, term, proposedCommands>>

ProcessCommitMsg(r, cmd) == 
  /\ cmd \in committed
  /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \ {cmd}]
  /\ UNCHANGED <<leader, uncommittedPool, committed, term, proposedCommands>>

LeaderChange(l) == 
  /\ l \in Replicas
  /\ leader' = l
  /\ term' = term + 1
  /\ LET allCommands == UNION { specPool[r] : r \in Replicas }
         count(cmd) == Cardinality({ r \in Replicas | cmd \in specPool[r] })
         recoveredCommands == { cmd \in allCommands | count(cmd) >= RecoverQuorumSize /\ cmd \notin committed }
     IN /\ uncommittedPool' = recoveredCommands
        /\ specPool' = [r \in Replicas |-> IF r = l THEN specPool[r] \cup recoveredCommands ELSE specPool[r] ]
  /\ UNCHANGED <<committed, proposedCommands>>

Next == 
  \/ \E cmd \in Commands : Propose(cmd)
  \/ \E r \in Replicas, cmd \in proposedCommands : ProcessProposeLeader(r, cmd)
  \/ \E r \in Replicas, cmd \in proposedCommands : ProcessProposeNonLeader(r, cmd)
  \/ \E cmd \in uncommittedPool : Commit(cmd)
  \/ \E r \in Replicas, cmd \in committed : ProcessCommitMsg(r, cmd)
  \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====