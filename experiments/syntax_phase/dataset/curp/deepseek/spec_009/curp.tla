---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags
CONSTANTS Replicas, Commands, Clients, Keys, keyOf, NULL
VARIABLES specPool, uncommittedPool, committed, leader, term, clientSeqs
vars == <<specPool, uncommittedPool, committed, leader, term, clientSeqs>>
Cardinality(S) == CHOOSE n \in Nat : \E f \in [1..n -> S] : \A x \in S : \E i \in 1..n : f[i] = x /\ \A i,j \in 1..n : i /= j => f[i] /= f[j]
N == Cardinality(Replicas)
Quorum == N \div 2 + 1
RecoverQuorum == Quorum \div 2 + 1
SuperQuorum == (N - Quorum) + RecoverQuorum
Init == 
    specPool = [r \in Replicas |-> {}] /\
    uncommittedPool = [r \in Replicas |-> {}] /\
    committed = {} /\
    leader = NULL /\
    term = 0 /\
    clientSeqs = [c \in Clients |-> 0]
Propose(c, cmd) == 
    /\ c \in Clients
    /\ cmd \in Commands
    /\ clientSeqs' = [clientSeqs EXCEPT ![c] = clientSeqs[c] + 1]
    /\ specPool' = [r \in Replicas |-> 
          LET conflict_spec == \E cmd2 \in specPool[r] : keyOf(cmd2) = keyOf(cmd) IN
          IF r = leader /\ leader /= NULL
          THEN 
              LET conflict_uncommitted == \E cmd2 \in uncommittedPool[r] : keyOf(cmd2) = keyOf(cmd) IN
              IF conflict_spec \/ conflict_uncommitted
              THEN specPool[r] \cup {cmd}
              ELSE specPool[r] \cup {cmd}
          ELSE specPool[r] \cup {cmd}
       ]
    /\ uncommittedPool' = [r \in Replicas |-> 
          LET conflict_spec == \E cmd2 \in specPool[r] : keyOf(cmd2) = keyOf(cmd) IN
          IF r = leader /\ leader /= NULL
          THEN 
              LET conflict_uncommitted == \E cmd2 \in uncommittedPool[r] : keyOf(cmd2) = keyOf(cmd) IN
              IF conflict_spec \/ conflict_uncommitted
              THEN uncommittedPool[r]
              ELSE uncommittedPool[r] \cup {cmd}
          ELSE uncommittedPool[r]
       ]
    /\ committed' = committed
    /\ leader' = leader
    /\ term' = term
Commit(cmd) == 
    /\ leader /= NULL
    /\ cmd \in uncommittedPool[leader]
    /\ \E S \subseteq Replicas : Cardinality(S) >= Quorum /\ \A r \in S : cmd \in uncommittedPool[r]
    /\ committed' = committed \cup {cmd}
    /\ UNCHANGED <<specPool, uncommittedPool, leader, term, clientSeqs>>
ProcessCommit(r) == 
    /\ r \in Replicas
    /\ specPool' = [specPool EXCEPT ![r] = specPool[r] \ committed] /\
    uncommittedPool' = [uncommittedPool EXCEPT ![r] = uncommittedPool[r] \ committed]
    /\ UNCHANGED <<committed, leader, term, clientSeqs>>
LeaderChange(l) == 
    /\ l \in Replicas
    /\ leader' = l /\
    term' = term + 1
    /\ LET recoveredSpec == { cmd \in Commands : \E S \subseteq Replicas : Cardinality(S) >= RecoverQuorum /\ \A r \in S : cmd \in specPool[r] } IN
       LET recoveredUncommitted == { cmd \in Commands : \E S \subseteq Replicas : Cardinality(S) >= RecoverQuorum /\ \A r \in S : cmd \in uncommittedPool[r] } IN
       specPool' = [specPool EXCEPT ![l] = recoveredSpec] /\
       uncommittedPool' = [uncommittedPool EXCEPT ![l] = recoveredUncommitted]
    /\ UNCHANGED <<committed, clientSeqs>>
Next == 
    \/ \E c \in Clients, cmd \in Commands : Propose(c, cmd)
    \/ \E cmd \in Commands : Commit(cmd)
    \/ \E r \in Replicas : ProcessCommit(r)
    \/ \E l \in Replicas : LeaderChange(l)
Spec == Init /\ [][Next]_vars
====