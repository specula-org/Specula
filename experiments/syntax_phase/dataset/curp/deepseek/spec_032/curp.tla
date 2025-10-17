---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Replicas, Keys, Values, Commands, Clients

VARIABLES
    replicaState,
    clientResponses,
    leader,
    backendLog,
    proposed,
    responded

vars == <<replicaState, clientResponses, leader, backendLog, proposed, responded>>

ReplicaState == [role: {"Leader", "Follower"}, specPool: SUBSET Commands, uncommittedPool: SUBSET Commands, committed: SUBSET Commands]

Key(cmd) == CHOOSE k \in Keys: TRUE

Conflict(cmd1, cmd2) == Key(cmd1) = Key(cmd2)

Quorum == Cardinality(Replicas) \div 2 + 1
SuperQuorum == (Cardinality(Replicas) - Quorum) + (Quorum \div 2 + 1)
RecoverQuorum == Quorum \div 2 + 1

Init ==
    /\ replicaState = [r \in Replicas |-> [role |-> "Follower", specPool |-> {}, uncommittedPool |-> {}, committed |-> {}]]
    /\ clientResponses = [c \in Clients |-> {}]
    /\ leader \in Replicas
    /\ backendLog = <<>>
    /\ proposed = {}
    /\ responded = {}

ClientPropose(c, cmd) ==
    /\ cmd \notin proposed
    /\ proposed' = proposed \cup {cmd}
    /\ replicaState' = [r \in Replicas |-> 
        IF r = leader
        THEN LET sp == replicaState[r].specPool IN
             LET ucp == replicaState[r].uncommittedPool IN
             IF \A otherCmd \in sp \cup ucp: ~Conflict(cmd, otherCmd)
             THEN [role |-> replicaState[r].role,
                   specPool |-> sp \cup {cmd},
                   uncommittedPool |-> ucp,
                   committed |-> replicaState[r].committed]
             ELSE [role |-> replicaState[r].role,
                   specPool |-> sp,
                   uncommittedPool |-> ucp \cup {cmd},
                   committed |-> replicaState[r].committed]
        ELSE LET sp == replicaState[r].specPool IN
             IF \A otherCmd \in sp: ~Conflict(cmd, otherCmd)
             THEN [role |-> replicaState[r].role,
                   specPool |-> sp \cup {cmd},
                   uncommittedPool |-> replicaState[r].uncommittedPool,
                   committed |-> replicaState[r].committed]
             ELSE replicaState[r]]
    /\ responded' = IF \E Q \in SUBSET (Replicas \ {leader}) : 
                      Cardinality(Q) >= SuperQuorum - 1 /\ 
                      (\A q \in Q: cmd \notin replicaState[q].specPool) \/ 
                      (\A q \in Q: cmd \in replicaState[q].specPool)
                   THEN responded \cup {cmd}
                   ELSE responded
    /\ UNCHANGED <<clientResponses, backendLog, leader>>

BackendCommit(cmd) ==
    /\ backendLog' = backendLog \o <<cmd>>
    /\ replicaState' = [r \in Replicas |-> 
        [role |-> replicaState[r].role,
         specPool |-> replicaState[r].specPool \ {cmd},
         uncommittedPool |-> replicaState[r].uncommittedPool \ {cmd},
         committed |-> replicaState[r].committed \cup {cmd}]]
    /\ clientResponses' = [c \in Clients |-> clientResponses[c] \cup {cmd}]
    /\ UNCHANGED <<leader, proposed, responded>>

LeaderChange(newLeader) ==
    /\ leader' = newLeader
    /\ \E Q \in SUBSET Replicas:
        Cardinality(Q) >= RecoverQuorum
        /\ LET allSpec == UNION {replicaState[q].specPool : q \in Q} IN
           LET recovered == {cmd \in allSpec: 
               Cardinality({q \in Q: cmd \in replicaState[q].specPool}) >= RecoverQuorum} IN
           replicaState' = [replicaState EXCEPT 
               ![newLeader] = [role |-> "Leader",
                               specPool |-> recovered,
                               uncommittedPool |-> recovered \ replicaState[newLeader].committed,
                               committed |-> replicaState[newLeader].committed]]
    /\ UNCHANGED <<clientResponses, backendLog, proposed, responded>>

Next ==
    \/ \E c \in Clients, cmd \in Commands: ClientPropose(c, cmd)
    \/ \E cmd \in Commands: BackendCommit(cmd)
    \/ \E newLeader \in Replicas: LeaderChange(newLeader)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====