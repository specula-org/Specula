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
    /\ \A r \in Replicas:
        IF r = leader
        THEN ProcessProposeLeader(r, cmd)
        ELSE ProcessProposeNonLeader(r, cmd)
    /\ UNCHANGED <<clientResponses, backendLog, leader, responded>>

ProcessProposeLeader(r, cmd) ==
    LET sp == replicaState[r].specPool
        ucp == replicaState[r].uncommittedPool
    IN
    /\ \A otherCmd \in sp \cup ucp: ~Conflict(cmd, otherCmd)
        => \/ \E Q \in SUBSET (Replicas \ {r}):
               /\ Cardinality(Q) >= SuperQuorum - 1
               /\ \A q \in Q: cmd \notin replicaState[q].specPool
               /\ replicaState' = [replicaState EXCEPT ![r].specPool = @ \cup {cmd}]
               /\ responded' = responded \cup {cmd}
           \/ \E Q \in SUBSET (Replicas \ {r}):
               /\ Cardinality(Q) >= SuperQuorum - 1
               /\ \A q \in Q: cmd \in replicaState[q].specPool
               /\ UNCHANGED replicaState
               /\ responded' = responded \cup {cmd}
    /\ \E otherCmd \in sp \cup ucp: Conflict(cmd, otherCmd)
        => /\ replicaState' = [replicaState EXCEPT ![r].uncommittedPool = @ \cup {cmd}]
           /\ UNCHANGED responded
    /\ UNCHANGED <<clientResponses, backendLog, leader, proposed>>

ProcessProposeNonLeader(r, cmd) ==
    LET sp == replicaState[r].specPool
    IN
    /\ \A otherCmd \in sp: ~Conflict(cmd, otherCmd)
        => /\ replicaState' = [replicaState EXCEPT ![r].specPool = @ \cup {cmd}]
           /\ UNCHANGED responded
    /\ \E otherCmd \in sp: Conflict(cmd, otherCmd)
        => UNCHANGED <<replicaState, responded>>
    /\ UNCHANGED <<clientResponses, backendLog, leader, proposed>>

BackendCommit(cmd) ==
    /\ backendLog' = backendLog \o <<cmd>>
    /\ \A r \in Replicas: ProcessCommit(r, cmd)
    /\ UNCHANGED <<clientResponses, leader, proposed, responded>>

ProcessCommit(r, cmd) ==
    /\ replicaState' = [replicaState EXCEPT 
        ![r].specPool = @ \ {cmd},
        ![r].uncommittedPool = @ \ {cmd},
        ![r].committed = @ \cup {cmd}]
    /\ clientResponses' = [c \in Clients |-> clientResponses[c] \cup {cmd}]
    /\ UNCHANGED <<backendLog, leader, proposed, responded>>

LeaderChange(newLeader) ==
    /\ leader' = newLeader
    /\ \E Q \in SUBSET Replicas:
        /\ Cardinality(Q) >= RecoverQuorum
        /\ LET allSpec == UNION {replicaState[q].specPool : q \in Q}
           IN
           LET recovered == {cmd \in allSpec: 
               Cardinality({q \in Q: cmd \in replicaState[q].specPool}) >= RecoverQuorum}
           IN
           replicaState' = [replicaState EXCEPT 
               ![newLeader] = [@ EXCEPT !.specPool = recovered,
                                        !.uncommittedPool = recovered \ replicaState[newLeader].committed]]
    /\ UNCHANGED <<clientResponses, backendLog, proposed, responded>>

Next ==
    \/ \E c \in Clients, cmd \in Commands: ClientPropose(c, cmd)
    \/ \E cmd \in Commands: BackendCommit(cmd)
    \/ \E newLeader \in Replicas: LeaderChange(newLeader)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====