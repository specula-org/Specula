---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Replicas, Commands, Keys, Key
\* Assume Key is a function from Commands to Keys.

N == Cardinality(Replicas)
Quorum == N \div 2 + 1
RecoverQuorum == Quorum \div 2 + 1
SuperQuorum == (N - Quorum) + RecoverQuorum

VARIABLES specPool, uncommittedPool, log, commitIndex, role, term, committed

vars == <<specPool, uncommittedPool, log, commitIndex, role, term, committed>>

Init == 
    /\ specPool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ log = [r \in Replicas |-> <<>>]
    /\ commitIndex = 0
    /\ role = [r \in Replicas |-> "Follower"]
    /\ term = [r \in Replicas |-> 1]
    /\ committed = {}

Propose(cmd) == 
    /\ cmd \in Commands
    /\ \A r \in Replicas : 
        IF \A c \in specPool[r] : Key(c) # Key(cmd)
        THEN specPool'[r] = specPool[r] \cup {cmd}
        ELSE specPool'[r] = specPool[r]
    /\ UNCHANGED <<uncommittedPool, log, commitIndex, role, term, committed>>

ProcessProposeLeader(r, cmd) == 
    /\ role[r] = "Leader"
    /\ cmd \in specPool[r]
    /\ \A c \in uncommittedPool[r] : Key(c) # Key(cmd)
    /\ uncommittedPool'[r] = uncommittedPool[r] \cup {cmd}
    /\ log'[r] = Append(log[r], cmd)
    /\ UNCHANGED <<specPool, commitIndex, role, term, committed>>

ProcessProposeNonLeader(r, cmd) == 
    /\ role[r] # "Leader"
    /\ cmd \in specPool[r]
    /\ UNCHANGED vars

Commit == 
    /\ \E leader \in Replicas : role[leader] = "Leader"
    /\ \E cmd \in uncommittedPool[leader] : cmd \notin committed
    /\ committed' = committed \cup {cmd}
    /\ UNCHANGED <<specPool, uncommittedPool, log, commitIndex, role, term>>

ProcessCommitMsg(r, cmd) == 
    /\ cmd \in committed
    /\ specPool'[r] = specPool[r] \ {cmd}
    /\ uncommittedPool'[r] = uncommittedPool[r] \ {cmd}
    /\ UNCHANGED <<log, commitIndex, role, term, committed>>

LeaderChange(l) == 
    /\ l \in Replicas
    /\ role[l] # "Leader"
    /\ role' = [r \in Replicas |-> IF r = l THEN "Leader" ELSE "Follower"]
    /\ term' = [r \in Replicas |-> IF r = l THEN term[r] + 1 ELSE term[r]]
    /\ \E Q \in SUBSET Replicas : Cardinality(Q) >= Quorum
    /\ LET recoveredSpec = Union({ specPool[r] : r \in Q }) IN
       specPool' = [r \in Replicas |-> IF r = l THEN recoveredSpec ELSE specPool[r]]
    /\ LET uncommittedCommands = { log[l][i] : i \in DOMAIN log[l] } \cap { c \in Commands : \E i \in DOMAIN log[l] : log[l][i] = c /\ i > commitIndex } IN
       uncommittedPool' = [r \in Replicas |-> IF r = l THEN uncommittedCommands ELSE uncommittedPool[r]]
    /\ UNCHANGED <<log, commitIndex, committed>>

Next == 
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====