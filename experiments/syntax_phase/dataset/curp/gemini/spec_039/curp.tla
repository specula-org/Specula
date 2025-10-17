---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Replicas,
    Commands,
    Keys,
    Key,      \* A function mapping a command to its key
    Nil       \* A default value

ASSUME \A c \in Commands : Key(c) \in Keys

VARIABLES
    leader,
    spec_pools,
    uncommitted_pool,
    committed_log,
    proposed_cmds,
    fast_path_acks

vars == <<leader, spec_pools, uncommitted_pool, committed_log, proposed_cmds, fast_path_acks>>

Quorum == Cardinality(Replicas) \div 2 + 1
RecoverQuorum == Quorum \div 2 + 1
SuperQuorum == (Cardinality(Replicas) - Quorum) + RecoverQuorum

Conflicts(cmd1, cmd2) == Key(cmd1) = Key(cmd2)
HasConflict(cmd, pool) == \E c2 \in pool : Conflicts(cmd, c2)

Init ==
    /\ \E r \in Replicas : leader = r
    /\ spec_pools = [r \in Replicas |-> {}]
    /\ uncommitted_pool = [r \in Replicas |-> {}]
    /\ committed_log = {}
    /\ proposed_cmds = {}
    /\ fast_path_acks = [cmd \in Commands |-> {}]

Propose(cmd) ==
    /\ cmd \in Commands
    /\ cmd \notin proposed_cmds
    /\ proposed_cmds' = proposed_cmds \cup {cmd}
    /\ UNCHANGED <<leader, spec_pools, uncommitted_pool, committed_log, fast_path_acks>>

ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ cmd \in proposed_cmds
    /\ r \notin fast_path_acks[cmd]
    /\ LET conflict == HasConflict(cmd, spec_pools[r]) \/ HasConflict(cmd, uncommitted_pool[r])
       IN IF conflict THEN
            /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \cup {cmd}]
            /\ spec_pools' = spec_pools
            /\ fast_path_acks' = fast_path_acks
       ELSE
            /\ spec_pools' = [spec_pools EXCEPT ![r] = @ \cup {cmd}]
            /\ fast_path_acks' = [fast_path_acks EXCEPT ![cmd] = @ \cup {r}]
            /\ uncommitted_pool' = uncommitted_pool
    /\ UNCHANGED <<leader, committed_log, proposed_cmds>>

ProcessProposeNonLeader(r, cmd) ==
    /\ r /= leader
    /\ cmd \in proposed_cmds
    /\ r \notin fast_path_acks[cmd]
    /\ LET conflict == HasConflict(cmd, spec_pools[r])
       IN IF \lnot conflict THEN
            /\ spec_pools' = [spec_pools EXCEPT ![r] = @ \cup {cmd}]
            /\ fast_path_acks' = [fast_path_acks EXCEPT ![cmd] = @ \cup {r}]
       ELSE
            /\ spec_pools' = spec_pools
            /\ fast_path_acks' = fast_path_acks
    /\ UNCHANGED <<leader, uncommitted_pool, committed_log, proposed_cmds>>

Commit ==
    /\ \E cmd \in uncommitted_pool[leader] :
        /\ committed_log' = committed_log \cup {cmd}
        /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![leader] = @ \ {cmd}]
        /\ UNCHANGED <<leader, spec_pools, proposed_cmds, fast_path_acks>>

ProcessCommitMsg(r, cmd) ==
    /\ r \in Replicas
    /\ cmd \in committed_log
    /\ cmd \in spec_pools[r]
    /\ spec_pools' = [spec_pools EXCEPT ![r] = @ \ {cmd}]
    /\ UNCHANGED <<leader, uncommitted_pool, committed_log, proposed_cmds, fast_path_acks>>

LeaderChange(l) ==
    /\ l \in Replicas
    /\ l /= leader
    /\ \E quorum_set \in {qs \in SUBSET Replicas : Cardinality(qs) >= Quorum} :
        /\ LET old_leader == leader
               all_spec_cmds == UNION {spec_pools[rep] : rep \in quorum_set}
               recovered_cmds == {c \in all_spec_cmds :
                                   Cardinality({rep \in quorum_set : c \in spec_pools[rep]}) >= RecoverQuorum}
           IN /\ leader' = l
              /\ spec_pools' = [spec_pools EXCEPT ![l] = @ \cup recovered_cmds]
              /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![l] = @ \cup recovered_cmds,
                                                       ![old_leader] = {}]
              /\ UNCHANGED <<committed_log, proposed_cmds, fast_path_acks>>

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====