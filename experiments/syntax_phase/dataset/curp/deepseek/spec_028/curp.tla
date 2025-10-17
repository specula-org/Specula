---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS Replicas, Clients, Keys, Cmds, NoOp, Nil

VARIABLES 
    role,
    specPool,
    uncommittedPool,
    committed,
    inflight,
    leader,
    term

vars == <<role, specPool, uncommittedPool, committed, inflight, leader, term>>

ReplicaSet == Replicas

Quorum(S) == Cardinality(S) \div 2 + 1
SuperQuorum(S) == (Cardinality(S) - Quorum(S)) + Quorum(Quorum(S))
RecoverQuorum(S) == Quorum(S) \div 2 + 1

KeysOf(cmd) == 
    IF cmd = NoOp THEN {}
    ELSE {cmd.key}

Conflicts(cmd1, cmd2) == 
    IF cmd1 = NoOp \/ cmd2 = NoOp THEN FALSE
    ELSE cmd1.key = cmd2.key

TypeOK == 
    /\ role \in [Replicas -> {"Leader", "Follower", "Candidate"}]
    /\ specPool \in [Replicas -> SUBSET Cmds]
    /\ uncommittedPool \in [Replicas -> SUBSET Cmds]
    /\ committed \in [Replicas -> SUBSET Cmds]
    /\ inflight \in [Clients -> SUBSET Cmds]
    /\ leader \in Replicas \cup {Nil}
    /\ term \in Nat

Init == 
    /\ role = [r \in Replicas |-> "Follower"]
    /\ specPool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ committed = [r \in Replicas |-> {}]
    /\ inflight = [c \in Clients |-> {}]
    /\ leader = Nil
    /\ term = 0

ClientPropose(c, cmd) == 
    /\ cmd \in Cmds
    /\ cmd \notin inflight[c]
    /\ inflight' = [inflight EXCEPT ![c] = @ \cup {cmd}]
    /\ UNCHANGED <<role, specPool, uncommittedPool, committed, leader, term>>

ProcessProposeLeader(r, cmd) == 
    /\ role[r] = "Leader"
    /\ ~\E c2 \in (specPool[r] \cup uncommittedPool[r]): Conflicts(cmd, c2)
    /\ specPool' = [specPool EXCEPT ![r] = @ \cup {cmd}]
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<role, committed, inflight, leader, term>>

ProcessProposeNonLeader(r, cmd) == 
    /\ role[r] \in {"Follower", "Candidate"}
    /\ ~\E c2 \in specPool[r]: Conflicts(cmd, c2)
    /\ specPool' = [specPool EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<role, uncommittedPool, committed, inflight, leader, term>>

Commit(cmd) == 
    /\ \E r \in Replicas: 
        /\ role[r] = "Leader"
        /\ cmd \in uncommittedPool[r]
        /\ LET committedReplicas == {s \in Replicas: cmd \in specPool[s]}
        IN Cardinality(committedReplicas) >= Quorum(Replicas)
    /\ committed' = [r \in Replicas |-> committed[r] \cup {cmd}]
    /\ specPool' = [r \in Replicas |-> specPool[r] \ {cmd}]
    /\ uncommittedPool' = [r \in Replicas |-> uncommittedPool[r] \ {cmd}]
    /\ inflight' = [c \in Clients |-> inflight[c] \ {cmd}]
    /\ UNCHANGED <<role, leader, term>>

ProcessCommitMsg(r, cmd) == 
    /\ cmd \in committed[r]
    /\ specPool' = [specPool EXCEPT ![r] = @ \ {cmd}]
    /\ uncommittedPool' = [uncommittedPool EXCEPT ![r] = @ \ {cmd}]
    /\ UNCHANGED <<role, committed, inflight, leader, term>>

LeaderChange(l) == 
    /\ l \in Replicas
    /\ role[l] = "Leader"
    /\ leader' = l
    /\ term' = term + 1
    /\ LET recoverSet == {s \in Replicas: Cardinality(specPool[s]) >= RecoverQuorum(Replicas)}
       IN /\ specPool' = [specPool EXCEPT ![l] = UNION {specPool[s] : s \in recoverSet}]
          /\ uncommittedPool' = [uncommittedPool EXCEPT ![l] = UNION {specPool[s] : s \in recoverSet}]
    /\ UNCHANGED <<role, committed, inflight>>

Next == 
    \/ \E c \in Clients, cmd \in Cmds: ClientPropose(c, cmd)
    \/ \E r \in Replicas, cmd \in Cmds: ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Cmds: ProcessProposeNonLeader(r, cmd)
    \/ \E cmd \in Cmds: Commit(cmd)
    \/ \E r \in Replicas, cmd \in Cmds: ProcessCommitMsg(r, cmd)
    \/ \E l \in Replicas: LeaderChange(l)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====