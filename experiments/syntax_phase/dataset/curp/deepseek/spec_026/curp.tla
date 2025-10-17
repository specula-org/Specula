---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Replicas, Commands, Clients, Keys, NULL

VARIABLES speculativePool, uncommittedPool, committed, committedIndex, leaderId, clientSequences, role, proposedCommands

Key(cmd) == CHOOSE k \in Keys : TRUE

vars == <<speculativePool, uncommittedPool, committed, committedIndex, leaderId, clientSequences, role, proposedCommands>>

N == Cardinality(Replicas)
QuorumSize == N \div 2 + 1
RecoverQuorum == QuorumSize \div 2 + 1

Init == 
    speculativePool = [r \in Replicas |-> {}] /\
    uncommittedPool = [r \in Replicas |-> {}] /\
    committed = {} /\
    committedIndex = 0 /\
    leaderId = NULL /\
    clientSequences = [c \in Clients |-> 0] /\
    role = [r \in Replicas |-> "Follower"] /\
    proposedCommands = {}

Propose(c, cmd) == 
    /\ c \in Clients
    /\ cmd \in Commands \ proposedCommands
    /\ clientSequences' = [clientSequences EXCEPT ![c] = clientSequences[c] + 1]
    /\ proposedCommands' = proposedCommands \cup {cmd}
    /\ UNCHANGED <<speculativePool, uncommittedPool, committed, committedIndex, leaderId, role>>

ProcessProposeLeader(r, cmd) == 
    /\ r \in Replicas
    /\ cmd \in proposedCommands
    /\ role[r] = "Leader"
    /\ cmd \notin committed
    /\ LET conflict == \E c1 \in speculativePool[r] : Key(c1) = Key(cmd) \/ \E c2 \in uncommittedPool[r] : Key(c2) = Key(cmd)
       IN IF conflict
          THEN uncommittedPool' = [uncommittedPool EXCEPT ![r] = uncommittedPool[r] \cup {cmd}]
          ELSE speculativePool' = [speculativePool EXCEPT ![r] = speculativePool[r] \cup {cmd}]
    /\ UNCHANGED <<committed, committedIndex, leaderId, clientSequences, role, proposedCommands>>

ProcessProposeNonLeader(r, cmd) == 
    /\ r \in Replicas
    /\ cmd \in proposedCommands
    /\ role[r] # "Leader"
    /\ cmd \notin committed
    /\ LET conflict == \E c1 \in speculativePool[r] : Key(c1) = Key(cmd)
       IN IF conflict
          THEN UNCHANGED speculativePool
          ELSE speculativePool' = [speculativePool EXCEPT ![r] = speculativePool[r] \cup {cmd}]
    /\ UNCHANGED <<uncommittedPool, committed, committedIndex, leaderId, clientSequences, role, proposedCommands>>

Commit(cmd) == 
    /\ cmd \in (UNION {uncommittedPool[r] : r \in Replicas}) \ committed
    /\ committed' = committed \cup {cmd}
    /\ committedIndex' = committedIndex + 1
    /\ UNCHANGED <<speculativePool, uncommittedPool, leaderId, clientSequences, role, proposedCommands>>

ProcessCommitMsg(r, cmd) == 
    /\ r \in Replicas
    /\ cmd \in committed
    /\ speculativePool' = [speculativePool EXCEPT ![r] = speculativePool[r] \ {cmd}]
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = uncommittedPool[r] \ {cmd}]
    /\ proposedCommands' = proposedCommands \ {cmd}
    /\ UNCHANGED <<committed, committedIndex, leaderId, clientSequences, role>>

LeaderChange(l, Q) == 
    /\ l \in Replicas
    /\ Q \in SUBSET Replicas
    /\ Cardinality(Q) >= QuorumSize
    /\ leaderId' = l
    /\ role' = [role EXCEPT ![l] = "Leader", ![r \in Replicas \ {l}] = "Follower"]
    /\ speculativePool' = [speculativePool EXCEPT ![l] = {cmd \in Commands : 
                Cardinality({s \in Q : cmd \in speculativePool[s]}) >= RecoverQuorum }]
    /\ UNCHANGED <<uncommittedPool, committed, committedIndex, clientSequences, proposedCommands>>

Next == 
    \/ \E c \in Clients, cmd \in Commands : Propose(c, cmd)
    \/ \E r \in Replicas, cmd \in proposedCommands : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in proposedCommands : ProcessProposeNonLeader(r, cmd)
    \/ \E cmd \in Commands : Commit(cmd)
    \/ \E r \in Replicas, cmd \in committed : ProcessCommitMsg(r, cmd)
    \/ \E l \in Replicas, Q \in SUBSET Replicas : LeaderChange(l, Q)

Spec == Init /\ [][Next]_vars

====