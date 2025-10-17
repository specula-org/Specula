---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Replicas, Clients, Keys, Values

VARIABLES leader, specPool, uncommittedPool, committed, msgs, clientNext

vars == <<leader, specPool, uncommittedPool, committed, msgs, clientNext>>

TypeInvariant ==
    /\ leader \in Replicas \union {NULL}
    /\ specPool \in [Replicas -> SUBSET(Commands)]
    /\ uncommittedPool \in [Replicas -> SUBSET(Commands)]
    /\ committed \subseteq Commands
    /\ msgs \subseteq Messages
    /\ clientNext \in [Clients -> Nat]

Commands == [client: Clients, seq: Nat, key: Keys, value: Values]

Messages == 
    {[type |-> "propose", cmd |-> cmd, replica |-> r]: cmd \in Commands, r \in Replicas} \cup
    {[type |-> "commit", cmd |-> cmd]: cmd \in Commands}

Quorum(n) == n \div 2 + 1
RecoverQuorum(n) == Quorum(n) \div 2 + 1

Conflicts(c1, c2) == c1.key = c2.key

Init ==
    /\ leader \in Replicas \union {NULL}
    /\ specPool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ committed = {}
    /\ msgs = {}
    /\ clientNext = [c \in Clients |-> 1]

ClientPropose(c, k, v) ==
    LET cmd == [client |-> c, seq |-> clientNext[c], key |-> k, value |-> v] IN
    /\ clientNext' = [clientNext EXCEPT ![c] = @ + 1]
    /\ msgs' = msgs \cup {[type |-> "propose", cmd |-> cmd, replica |-> r] : r \in Replicas}
    /\ UNCHANGED <<leader, specPool, uncommittedPool, committed>>

ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ [type |-> "propose", cmd |-> cmd, replica |-> r] \in msgs
    /\ specPool' = [specPool EXCEPT ![r] = @ \cup {cmd}]
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \cup {cmd}]
    /\ msgs' = msgs \ {[type |-> "propose", cmd |-> cmd, replica |-> r]}
    /\ UNCHANGED <<leader, committed, clientNext>>

ProcessProposeNonLeader(r, cmd) ==
    /\ r # leader
    /\ [type |-> "propose", cmd |-> cmd, replica |-> r] \in msgs
    /\ specPool' = [specPool EXCEPT ![r] = @ \cup {cmd}]
    /\ msgs' = msgs \ {[type |-> "propose", cmd |-> cmd, replica |-> r]}
    /\ UNCHANGED <<leader, uncommittedPool, committed, clientNext>>

Commit(cmd) ==
    /\ leader # NULL
    /\ cmd \in uncommittedPool[leader]
    /\ committed' = committed \cup {cmd}
    /\ msgs' = msgs \cup {[type |-> "commit", cmd |-> cmd]}
    /\ UNCHANGED <<leader, specPool, uncommittedPool, clientNext>>

ProcessCommitMsg(r, cmd) ==
    /\ [type |-> "commit", cmd |-> cmd] \in msgs
    /\ specPool' = [specPool EXCEPT ![r] = @ \ {cmd}]
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \ {cmd}]
    /\ clientNext' = [c \in Clients |-> IF c = cmd.client THEN Max(clientNext[c], cmd.seq + 1) ELSE clientNext[c]]
    /\ msgs' = msgs \ {[type |-> "commit", cmd |-> cmd]}
    /\ UNCHANGED <<leader, committed>>

LeaderChange(newLeader) ==
    /\ newLeader \in Replicas
    /\ leader' = newLeader
    /\ LET n == Cardinality(Replicas) IN
       LET Q == Quorum(n) IN
       LET RQ == RecoverQuorum(n) IN
       LET allSpec == UNION({specPool[r] : r \in Replicas}) IN
       LET recoveredSpec == {cmd \in allSpec : Cardinality({r \in Replicas : cmd \in specPool[r]}) >= RQ} IN
       LET recoveredUncommitted == {cmd \in allSpec : Cardinality({r \in Replicas : cmd \in specPool[r]}) >= Q} IN
       /\ specPool' = [specPool EXCEPT ![newLeader] = recoveredSpec \ committed]
       /\ uncommittedPool' = [uncommittedPool EXCEPT ![newLeader] = recoveredUncommitted \ committed]
    /\ UNCHANGED <<committed, msgs, clientNext>>

Next ==
    \/ \E c \in Clients, k \in Keys, v \in Values: ClientPropose(c, k, v)
    \/ \E r \in Replicas, cmd \in Commands: ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands: ProcessProposeNonLeader(r, cmd)
    \/ \E cmd \in Commands: Commit(cmd)
    \/ \E r \in Replicas, cmd \in Commands: ProcessCommitMsg(r, cmd)
    \/ \E newLeader \in Replicas: LeaderChange(newLeader)

====