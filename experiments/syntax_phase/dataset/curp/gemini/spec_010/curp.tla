---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS 
    Replicas,
    Keys,
    Nil

Commands == {[key |-> k, val |-> v] : k \in Keys, v \in {1}}

ASSUME
    /\ IsFiniteSet(Replicas)
    /\ IsFiniteSet(Commands)
    /\ IsFiniteSet(Keys)
    /\ Nil \notin Replicas
    /\ \A cmd \in Commands : cmd["key"] \in Keys

VARIABLES 
    term,
    leader,
    log,
    commitIndex,
    lastApplied,
    spec_pool,
    uncommitted_pool,
    client_proposals

vars == <<term, leader, log, commitIndex, lastApplied, spec_pool, uncommitted_pool, client_proposals>>

Quorum(S) == Cardinality(S) \div 2 + 1
RecoverQuorum(S) == Quorum(S) \div 2 + 1

GetKeys(cmd) == {cmd["key"]}

Conflicts(cmd, pool) ==
    \E p_cmd \in pool : GetKeys(cmd) \cap GetKeys(p_cmd) /= {}

Init ==
    /\ term = 0
    /\ leader = Nil
    /\ log = [r \in Replicas |-> <<>>]
    /\ commitIndex = [r \in Replicas |-> 0]
    /\ lastApplied = [r \in Replicas |-> 0]
    /\ spec_pool = [r \in Replicas |-> {}]
    /\ uncommitted_pool = [r \in Replicas |-> {}]
    /\ client_proposals = EmptyBag

Propose(cmd) ==
    /\ client_proposals' = client_proposals \+ (cmd :> Cardinality(Replicas))
    /\ UNCHANGED <<term, leader, log, commitIndex, lastApplied, spec_pool, uncommitted_pool>>

ProcessProposeLeader(r, cmd) ==
    LET conflict_spec == Conflicts(cmd, spec_pool[r])
        conflict_ucp == Conflicts(cmd, uncommitted_pool[r])
    IN
        /\ r = leader
        /\ BagCount(cmd, client_proposals) > 0
        /\ client_proposals' = client_proposals \- (cmd :> 1)
        /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \cup {cmd}]
        /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \cup {cmd}]
        /\ log' = [log EXCEPT ![r] = Append(@, cmd)]
        /\ UNCHANGED <<term, leader, commitIndex, lastApplied>>

ProcessProposeNonLeader(r, cmd) ==
    LET conflict_spec == Conflicts(cmd, spec_pool[r])
    IN
        /\ r /= leader
        /\ leader /= Nil
        /\ BagCount(cmd, client_proposals) > 0
        /\ client_proposals' = client_proposals \- (cmd :> 1)
        /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \cup {cmd}]
        /\ UNCHANGED <<term, leader, log, commitIndex, lastApplied, uncommitted_pool>>

Commit ==
    /\ leader /= Nil
    /\ \E cmd_index \in (commitIndex[leader] + 1) .. Len(log[leader]) :
        LET cmd == log[leader][cmd_index]
        IN LET replicators == {r \in Replicas : 
                                /\ cmd_index \in DOMAIN log[r] 
                                /\ log[r][cmd_index] = cmd}
           IN /\ Cardinality(replicators) >= Quorum(Replicas)
              /\ commitIndex' = [commitIndex EXCEPT ![leader] = cmd_index]
    /\ UNCHANGED <<term, leader, log, lastApplied, spec_pool, uncommitted_pool, client_proposals>>

FollowerUpdateCommitIndex(r) ==
    /\ r /= leader
    /\ leader /= Nil
    /\ commitIndex[r] < commitIndex[leader]
    /\ commitIndex' = [commitIndex EXCEPT ![r] = Min(commitIndex[leader], Len(log[r]))]
    /\ UNCHANGED <<term, leader, log, lastApplied, spec_pool, uncommitted_pool, client_proposals>>

ProcessCommitMsg(r) ==
    /\ commitIndex[r] > lastApplied[r]
    /\ LET apply_idx == lastApplied[r] + 1
       IN LET cmd_to_apply == log[r][apply_idx]
          IN /\ lastApplied' = [lastApplied EXCEPT ![r] = apply_idx]
             /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \ {cmd_to_apply}]
             /\ uncommitted_pool' = IF r = leader
                                    THEN [uncommitted_pool EXCEPT ![r] = @ \ {cmd_to_apply}]
                                    ELSE uncommitted_pool
    /\ UNCHANGED <<term, leader, log, commitIndex, client_proposals>>

LeaderChange(new_leader) ==
    /\ \E voters \in SUBSET Replicas : (* SANY error fix: Changed `\subseteq` to `\in SUBSET` for quantifier syntax *)
        /\ Cardinality(voters) >= Quorum(Replicas)
        /\ new_leader \in voters
        /\ term' = term + 1
        /\ leader' = new_leader
        /\ LET all_spec_cmds == UNION {spec_pool[v] : v \in voters}
               recovered_cmds == { cmd \in all_spec_cmds : 
                                    Cardinality({v \in voters : cmd \in spec_pool[v]}) >= RecoverQuorum(voters) }
           IN \E new_entries \in Permutations(recovered_cmds) :
                LET new_leader_log == log[new_leader] \o new_entries
                    new_uncommitted == { new_leader_log[i] : i \in (commitIndex[new_leader] + 1) .. Len(new_leader_log) }
                    new_spec == { new_leader_log[i] : i \in (lastApplied[new_leader] + 1) .. Len(new_leader_log) }
                IN /\ log' = [log EXCEPT ![new_leader] = new_leader_log]
                   /\ uncommitted_pool' = [r \in Replicas |-> IF r = new_leader THEN new_uncommitted ELSE {}]
                   /\ spec_pool' = [spec_pool EXCEPT ![new_leader] = new_spec]
    /\ UNCHANGED <<commitIndex, lastApplied, client_proposals>>

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in DOMAIN client_proposals : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in DOMAIN client_proposals : ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas : FollowerUpdateCommitIndex(r)
    \/ \E r \in Replicas : ProcessCommitMsg(r)
    \/ \E new_leader \in Replicas : LeaderChange(new_leader)

Spec == Init /\ [][Next]_vars

====