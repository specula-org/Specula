---- MODULE curp ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS 
    Replicas,
    Commands,
    Keys

VARIABLES
    replicaState,
    speculativePool,
    uncommittedPool,
    committedCommands,
    currentLeader,
    clientResponses,
    messages

vars == <<replicaState, speculativePool, uncommittedPool, committedCommands, currentLeader, clientResponses, messages>>

ASSUME 
    /\ Replicas # {}
    /\ Commands # {}
    /\ Keys # {}
    /\ Cardinality(Replicas) >= 3

Quorum == Cardinality(Replicas) \div 2 + 1
SuperQuorum == (Cardinality(Replicas) - Quorum) + ((Quorum \div 2) + 1)
RecoverQuorum == (Quorum \div 2) + 1

CommandKeys(cmd) == CHOOSE k \in SUBSET Keys : TRUE

ConflictsWith(cmd1, cmd2) == CommandKeys(cmd1) \cap CommandKeys(cmd2) # {}

TypeOK ==
    /\ replicaState \in [Replicas -> {"follower", "leader"}]
    /\ speculativePool \in [Replicas -> SUBSET Commands]
    /\ uncommittedPool \in [Replicas -> SUBSET Commands]
    /\ committedCommands \subseteq Commands
    /\ currentLeader \in Replicas \cup {NoLeader}
    /\ clientResponses \in [Commands -> {"none", "fast", "slow"}]
    /\ messages \subseteq [type: {"propose", "commit", "leader_change"}, 
                          cmd: Commands \cup {NoCommand}, 
                          from: Replicas, 
                          to: Replicas]

NoLeader == CHOOSE x : x \notin Replicas
NoCommand == CHOOSE x : x \notin Commands

Init ==
    /\ replicaState = [r \in Replicas |-> "follower"]
    /\ speculativePool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ committedCommands = {}
    /\ currentLeader = NoLeader
    /\ clientResponses = [cmd \in Commands |-> "none"]
    /\ messages = {}

HasConflictInPool(cmd, pool) ==
    \E existing \in pool : ConflictsWith(cmd, existing)

Propose(cmd) ==
    /\ cmd \in Commands
    /\ clientResponses[cmd] = "none"
    /\ messages' = messages \cup {[type |-> "propose", cmd |-> cmd, from |-> NoLeader, to |-> r] : r \in Replicas}
    /\ UNCHANGED <<replicaState, speculativePool, uncommittedPool, committedCommands, currentLeader, clientResponses>>

ProcessProposeLeader(r, cmd) ==
    /\ r \in Replicas
    /\ replicaState[r] = "leader"
    /\ currentLeader = r
    /\ [type |-> "propose", cmd |-> cmd, from |-> NoLeader, to |-> r] \in messages
    /\ cmd \notin committedCommands
    /\ LET hasConflict == HasConflictInPool(cmd, speculativePool[r]) \/ HasConflictInPool(cmd, uncommittedPool[r])
       IN /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \cup {cmd}]
          /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \cup {cmd}]
          /\ IF ~hasConflict
             THEN /\ clientResponses' = [clientResponses EXCEPT ![cmd] = "fast"]
                  /\ messages' = messages
             ELSE /\ clientResponses' = clientResponses
                  /\ messages' = messages
    /\ UNCHANGED <<replicaState, committedCommands, currentLeader>>

ProcessProposeNonLeader(r, cmd) ==
    /\ r \in Replicas
    /\ replicaState[r] = "follower"
    /\ [type |-> "propose", cmd |-> cmd, from |-> NoLeader, to |-> r] \in messages
    /\ cmd \notin committedCommands
    /\ LET hasConflict == HasConflictInPool(cmd, speculativePool[r])
       IN /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \cup {cmd}]
          /\ UNCHANGED <<replicaState, uncommittedPool, committedCommands, currentLeader, clientResponses, messages>>

Commit(cmd) ==
    /\ cmd \in Commands
    /\ cmd \notin committedCommands
    /\ \E r \in Replicas : cmd \in uncommittedPool[r]
    /\ committedCommands' = committedCommands \cup {cmd}
    /\ messages' = messages \cup {[type |-> "commit", cmd |-> cmd, from |-> NoLeader, to |-> r] : r \in Replicas}
    /\ UNCHANGED <<replicaState, speculativePool, uncommittedPool, currentLeader, clientResponses>>

ProcessCommitMsg(r, cmd) ==
    /\ r \in Replicas
    /\ [type |-> "commit", cmd |-> cmd, from |-> NoLeader, to |-> r] \in messages
    /\ cmd \in committedCommands
    /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \ {cmd}]
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \ {cmd}]
    /\ IF clientResponses[cmd] = "none"
       THEN clientResponses' = [clientResponses EXCEPT ![cmd] = "slow"]
       ELSE clientResponses' = clientResponses
    /\ UNCHANGED <<replicaState, committedCommands, currentLeader, messages>>

LeaderChange(newLeader) ==
    /\ newLeader \in Replicas
    /\ currentLeader # newLeader
    /\ LET quorumReplicas == CHOOSE S \in SUBSET Replicas : 
                               /\ Cardinality(S) = Quorum
                               /\ newLeader \in S
           recoveredSpecs == UNION {speculativePool[r] : r \in quorumReplicas}
           recoveredUncommitted == {cmd \in recoveredSpecs : 
                                     Cardinality({r \in quorumReplicas : cmd \in speculativePool[r]}) >= RecoverQuorum}
       IN /\ replicaState' = [r \in Replicas |-> IF r = newLeader THEN "leader" ELSE "follower"]
          /\ currentLeader' = newLeader
          /\ speculativePool' = [r \in Replicas |-> 
                                  IF r = newLeader 
                                  THEN recoveredSpecs \ committedCommands
                                  ELSE speculativePool[r]]
          /\ uncommittedPool' = [r \in Replicas |-> 
                                  IF r = newLeader 
                                  THEN recoveredUncommitted \ committedCommands
                                  ELSE uncommittedPool[r]]
          /\ messages' = messages \cup {[type |-> "leader_change", cmd |-> NoCommand, from |-> newLeader, to |-> r] : r \in Replicas}
    /\ UNCHANGED <<committedCommands, clientResponses>>

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
    \/ \E cmd \in Commands : Commit(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
    \/ \E r \in Replicas : LeaderChange(r)

Spec == Init /\ [][Next]_vars

====