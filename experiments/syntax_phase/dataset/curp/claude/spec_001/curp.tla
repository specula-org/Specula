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
             THEN clientResponses' = [clientResponses EXCEPT ![cmd] = "fast"]
             ELSE clientResponses' = clientResponses
          /\ messages' = messages \ {[type |-> "propose", cmd |-> cmd, from |-> NoLeader, to |-> r]}
          /\ UNCHANGED <<replicaState, committedCommands, currentLeader>>

ProcessProposeNonLeader(r, cmd) ==
    /\ r \in Replicas
    /\ replicaState[r] = "follower"
    /\ [type |-> "propose", cmd |-> cmd, from |-> NoLeader, to |-> r] \in messages
    /\ cmd \notin committedCommands
    /\ LET hasConflict == HasConflictInPool(cmd, speculativePool[r])
       IN /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \cup {cmd}]
          /\ messages' = messages \ {[type |-> "propose", cmd |-> cmd, from |-> NoLeader, to |-> r]}
          /\ UNCHANGED <<replicaState, uncommittedPool, committedCommands, currentLeader, clientResponses>>

Commit ==
    /\ currentLeader # NoLeader
    /\ \E cmd \in Commands :
        /\ cmd \in uncommittedPool[currentLeader]
        /\ cmd \notin committedCommands
        /\ committedCommands' = committedCommands \cup {cmd}
        /\ messages' = messages \cup {[type |-> "commit", cmd |-> cmd, from |-> currentLeader, to |-> r] : r \in Replicas}
        /\ IF clientResponses[cmd] = "none"
           THEN clientResponses' = [clientResponses EXCEPT ![cmd] = "slow"]
           ELSE clientResponses' = clientResponses
        /\ UNCHANGED <<replicaState, speculativePool, uncommittedPool, currentLeader>>

ProcessCommitMsg(r, cmd) ==
    /\ r \in Replicas
    /\ [type |-> "commit", cmd |-> cmd, from |-> currentLeader, to |-> r] \in messages
    /\ cmd \in committedCommands
    /\ speculativePool' = [speculativePool EXCEPT ![r] = @ \ {cmd}]
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \ {cmd}]
    /\ messages' = messages \ {[type |-> "commit", cmd |-> cmd, from |-> currentLeader, to |-> r]}
    /\ UNCHANGED <<replicaState, committedCommands, currentLeader, clientResponses>>

LeaderChange(newLeader) ==
    /\ newLeader \in Replicas
    /\ newLeader # currentLeader
    /\ LET quorumReplicas == CHOOSE S \in SUBSET Replicas : 
                               /\ newLeader \in S 
                               /\ Cardinality(S) >= Quorum
           recoveredSpecs == UNION {speculativePool[r] : r \in quorumReplicas}
           recoveredUncommitted == {cmd \in recoveredSpecs : 
                                     Cardinality({r \in quorumReplicas : cmd \in speculativePool[r]}) >= RecoverQuorum}
       IN /\ currentLeader' = newLeader
          /\ replicaState' = [r \in Replicas |-> IF r = newLeader THEN "leader" ELSE "follower"]
          /\ speculativePool' = [speculativePool EXCEPT ![newLeader] = recoveredSpecs]
          /\ uncommittedPool' = [uncommittedPool EXCEPT ![newLeader] = recoveredUncommitted]
          /\ messages' = messages \cup {[type |-> "leader_change", cmd |-> NoCommand, from |-> newLeader, to |-> r] : r \in Replicas}
          /\ UNCHANGED <<committedCommands, clientResponses>>

ProcessLeaderChangeMsg(r) ==
    /\ r \in Replicas
    /\ r # currentLeader
    /\ [type |-> "leader_change", cmd |-> NoCommand, from |-> currentLeader, to |-> r] \in messages
    /\ replicaState' = [replicaState EXCEPT ![r] = "follower"]
    /\ messages' = messages \ {[type |-> "leader_change", cmd |-> NoCommand, from |-> currentLeader, to |-> r]}
    /\ UNCHANGED <<speculativePool, uncommittedPool, committedCommands, currentLeader, clientResponses>>

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
    \/ \E newLeader \in Replicas : LeaderChange(newLeader)
    \/ \E r \in Replicas : ProcessLeaderChangeMsg(r)

Spec == Init /\ [][Next]_vars

====