---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Replicas, Commands, Quorum, SuperQuorum, RecoverQuorum, Key, Value

VARIABLES
    leader,
    specPool,
    uncommittedPool,
    committed,
    responded

vars == <<leader, specPool, uncommittedPool, committed, responded>>

Init ==
    /\ leader \in Replicas
    /\ specPool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ committed = {}
    /\ responded = {}

Key(c) == c.key

Conflict(c1, c2) == Key(c1) = Key(c2)

HasConflict(c, s) == \E x \in s : Conflict(c, x)

ProcessProposeLeader(r, c) ==
    /\ r = leader
    /\ c \notin responded
    /\ LET combined == specPool[r] \cup uncommittedPool[r]
       IN
       IF ~HasConflict(c, combined)
       THEN
           /\ responded' = responded \cup {c}
           /\ specPool' = [rr \in Replicas |-> specPool[rr] \cup {c}]
           /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \cup {c}]
           /\ committed' = committed
       ELSE
           /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \cup {c}]
           /\ UNCHANGED <<specPool, responded, committed>>

ProcessProposeNonLeader(r, c) ==
    /\ r # leader
    /\ c \notin responded
    /\ IF ~HasConflict(c, specPool[r])
       THEN
           /\ specPool' = [specPool EXCEPT ![r] = @ \cup {c}]
           /\ UNCHANGED <<uncommittedPool, responded, committed>>
       ELSE
           /\ UNCHANGED <<specPool, uncommittedPool, responded, committed>>

Commit(c) ==
    /\ c \notin committed
    /\ committed' = committed \cup {c}
    /\ specPool' = [r \in Replicas |-> specPool[r] \ {c}]
    /\ uncommittedPool' = [r \in Replicas |-> uncommittedPool[r] \ {c}]
    /\ responded' = responded \cup {c}

LeaderChange(newLeader) ==
    /\ newLeader # leader
    /\ \E Q \in SUBSET Replicas :
        /\ Cardinality(Q) >= Quorum
        /\ LET allSpec == UNION {specPool[r] : r \in Q}
           recovered == {c \in allSpec : 
               Cardinality({r \in Q : c \in specPool[r]}) >= RecoverQuorum}
           IN
           /\ specPool' = [specPool EXCEPT ![newLeader] = (specPool[newLeader] \ committed) \cup (recovered \ committed)]
           /\ uncommittedPool' = [uncommittedPool EXCEPT ![newLeader] = (uncommittedPool[newLeader] \ committed) \cup (recovered \ committed)]
    /\ leader' = newLeader
    /\ UNCHANGED <<committed, responded>>

Next ==
    \/ \E r \in Replicas, c \in Commands : ProcessProposeLeader(r, c)
    \/ \E r \in Replicas, c \in Commands : ProcessProposeNonLeader(r, c)
    \/ \E c \in Commands : Commit(c)
    \/ \E newLeader \in Replicas : LeaderChange(newLeader)

====