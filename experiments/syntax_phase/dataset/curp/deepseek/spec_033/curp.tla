---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Replicas, Commands, Keys, keyOf
ASSUME Replicas # {}
ASSUME Commands # {}
ASSUME Keys # {}
ASSUME keyOf \in [Commands -> Keys]
VARIABLES leader, specPool, uncommittedPool, committed, recvCmds
vars == <<leader, specPool, uncommittedPool, committed, recvCmds>>
N == Cardinality(Replicas)
Quorum == (N \div 2) + 1
RecoverQuorum == (Quorum \div 2) + 1
Init == 
  /\ leader \in Replicas
  /\ specPool = [r \in Replicas |-> {}]
  /\ uncommittedPool = [r \in Replicas |-> {}]
  /\ committed = {}
  /\ recvCmds = [r \in Replicas |-> {}]
Propose(cmd) == 
  /\ recvCmds' = [r \in Replicas |-> recvCmds[r] \cup {cmd}]
  /\ UNCHANGED <<leader, specPool, uncommittedPool, committed>>
ProcessProposeLeader(r, cmd) == 
  /\ r = leader
  /\ cmd \in recvCmds[r]
  /\ LET conflict == \E c \in specPool[r] \cup uncommittedPool[r] : keyOf(c) = keyOf(cmd)
    IN
    IF ~conflict
      THEN
        /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {cmd}]
        /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = uncommittedPool[r] \cup {cmd}]
        /\ recvCmds' = [recvCmds EXCEPT ![r] = recvCmds[r] \ {cmd}]
        /\ UNCHANGED <<leader, committed>>
      ELSE
        /\ recvCmds' = [recvCmds EXCEPT ![r] = recvCmds[r] \ {cmd}]
        /\ UNCHANGED <<leader, specPool, uncommittedPool, committed>>
ProcessProposeNonLeader(r, cmd) == 
  /\ r # leader
  /\ cmd \in recvCmds[r]
  /\ LET conflict == \E c \in specPool[r] : keyOf(c) = keyOf(cmd)
    IN
    IF ~conflict
      THEN
        /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \cup {cmd}]
        /\ UNCHANGED uncommittedPool
        /\ recvCmds' = [recvCmds EXCEPT ![r] = recvCmds[r] \ {cmd}]
        /\ UNCHANGED <<leader, committed>>
      ELSE
        /\ recvCmds' = [recvCmds EXCEPT ![r] = recvCmds[r] \ {cmd}]
        /\ UNCHANGED <<leader, specPool, uncommittedPool, committed>>
Commit(cmd) == 
  /\ cmd \notin committed
  /\ committed' = committed \cup {cmd}
  /\ UNCHANGED <<leader, specPool, uncommittedPool, recvCmds>>
ProcessCommitMsg(r, cmd) == 
  /\ cmd \in committed
  /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \ {cmd}]
  /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = uncommittedPool[r] \ {cmd}]
  /\ UNCHANGED <<leader, committed, recvCmds>>
LeaderChange(l) == 
  /\ l \in Replicas
  /\ leader # l
  /\ \E Q \in SUBSET (Replicas \ {l}) : 
        Cardinality(Q) >= RecoverQuorum
        /\ LET S == {cmd \in Commands : \exists r \in Q : cmd \in specPool[r]}
          IN
          /\ specPool' = [specPool EXCEPT ![l] = specPool[l] \cup {cmd \in S : cmd \notin committed}]
          /\ uncommittedPool' = [uncommittedPool EXCEPT ![l] = uncommittedPool[l] \cup {cmd \in S : cmd \notin committed}]
          /\ leader' = l
          /\ UNCHANGED <<committed, recvCmds>>
Next == 
  \/ \E cmd \in Commands : Propose(cmd)
  \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
  \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
  \/ \E cmd \in Commands : Commit(cmd)
  \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
  \/ \E l \in Replicas : LeaderChange(l)
Spec == Init /\ [][Next]_vars
====