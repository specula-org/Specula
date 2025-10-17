---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    Replicas,
    Keys,
    Values

VARIABLES
    leader,
    term,
    speculative_pool,
    uncommitted_pool,
    committed_cmds,
    applied_cmds,
    proposal_status,
    pending_proposals,
    new_leader_recovered

vars == << leader, term, speculative_pool, uncommitted_pool, committed_cmds, applied_cmds, proposal_status, pending_proposals, new_leader_recovered >>

Commands == [key: Keys, val: Values]

Quorum(n) == n \div 2 + 1
RecoverQuorum(n) == Quorum(n) \div 2 + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

Conflicts(cmd1, cmd2) == cmd1["key"] = cmd2["key"]

Init ==
    /\ \E r \in Replicas : leader = r
    /\ term = 1
    /\ speculative_pool = [r \in Replicas |-> {}]
    /\ uncommitted_pool = [r \in Replicas |-> {}]
    /\ committed_cmds = {}
    /\ applied_cmds = [r \in Replicas |-> {}]
    /\ proposal_status = [r \in Replicas |-> [c \in {} |-> [conflict |-> FALSE]]]
    /\ pending_proposals = [r \in Replicas |-> {}]
    /\ new_leader_recovered = TRUE

Propose(cmd) ==
    LET AllCmds ==
        (UNION {speculative_pool[r] : r \in Replicas}) \cup
        (UNION {uncommitted_pool[r] : r \in Replicas}) \cup
        committed_cmds \cup
        (UNION {applied_cmds[r] : r \in Replicas}) \cup
        (UNION {pending_proposals[r] : r \in Replicas})
    IN
        /\ cmd \notin AllCmds
        /\ pending_proposals' = [r \in Replicas |-> pending_proposals[r] \cup {cmd}]
        /\ UNCHANGED << leader, term, speculative_pool, uncommitted_pool, committed_cmds, applied_cmds, proposal_status, new_leader_recovered >>

ProcessProposeLeader(r, cmd) ==
    LET
        conflicts_sp == \E c \in speculative_pool[r] : Conflicts(c, cmd)
        conflicts_ucp == \E c \in uncommitted_pool[r] : Conflicts(c, cmd)
        has_conflict == conflicts_sp \/ conflicts_ucp
    IN
        /\ r = leader
        /\ new_leader_recovered = TRUE
        /\ cmd \in pending_proposals[r]
        /\ speculative_pool' = [speculative_pool EXCEPT ![r] = @ \cup {cmd}]
        /\ uncommitted_pool' = IF has_conflict
                               THEN uncommitted_pool
                               ELSE [uncommitted_pool EXCEPT ![r] = @ \cup {cmd}]
        /\ proposal_status' = [proposal_status EXCEPT ![r] = [proposal_status[r] EXCEPT ![cmd] = [conflict |-> has_conflict]]]
        /\ pending_proposals' = [pending_proposals EXCEPT ![r] = @ \ {cmd}]
        /\ UNCHANGED << leader, term, committed_cmds, applied_cmds, new_leader_recovered >>

ProcessProposeNonLeader(r, cmd) ==
    LET has_conflict == \E c \in speculative_pool[r] : Conflicts(c, cmd)
    IN
        /\ r /= leader
        /\ cmd \in pending_proposals[r]
        /\ speculative_pool' = [speculative_pool EXCEPT ![r] = @ \cup {cmd}]
        /\ proposal_status' = [proposal_status EXCEPT ![r] = [proposal_status[r] EXCEPT ![cmd] = [conflict |-> has_conflict]]]
        /\ pending_proposals' = [pending_proposals EXCEPT ![r] = @ \ {cmd}]
        /\ UNCHANGED << leader, term, uncommitted_pool, committed_cmds, applied_cmds, new_leader_recovered >>

Commit ==
    /\ new_leader_recovered = TRUE
    /\ \E cmd \in uncommitted_pool[leader]:
        /\ cmd \notin committed_cmds
        /\ LET Acks == {r \in Replicas : cmd \in speculative_pool[r]}
           IN Cardinality(Acks) >= Quorum(Cardinality(Replicas))
        /\ committed_cmds' = committed_cmds \cup {cmd}
        /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![leader] = @ \ {cmd}]
        /\ UNCHANGED << leader, term, speculative_pool, applied_cmds, proposal_status, pending_proposals, new_leader_recovered >>

ProcessCommitMsg(r, cmd) ==
    /\ cmd \in committed_cmds
    /\ cmd \notin applied_cmds[r]
    /\ speculative_pool' = [speculative_pool EXCEPT ![r] = @ \ {cmd}]
    /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \ {cmd}]
    /\ applied_cmds' = [applied_cmds EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED << leader, term, committed_cmds, proposal_status, pending_proposals, new_leader_recovered >>

LeaderChange(l) ==
    /\ l \in Replicas
    /\ l /= leader
    /\ leader' = l
    /\ term' = term + 1
    /\ new_leader_recovered' = FALSE
    /\ UNCHANGED << speculative_pool, uncommitted_pool, committed_cmds, applied_cmds, proposal_status, pending_proposals >>

LeaderRecovery(r) ==
    /\ r = leader
    /\ new_leader_recovered = FALSE
    /\ \E Q \in SUBSET Replicas:
        /\ Cardinality(Q) >= Quorum(Cardinality(Replicas))
        /\ LET
            AllSPCmds == UNION {speculative_pool[q] : q \in Q}
            RecoveredCmds == {c \in AllSPCmds : Cardinality({q \in Q : c \in speculative_pool[q]}) >= RecoverQuorum(Cardinality(Replicas))}
           IN
            /\ speculative_pool' = [speculative_pool EXCEPT ![r] = RecoveredCmds]
            /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = RecoveredCmds]
            /\ new_leader_recovered' = TRUE
            /\ UNCHANGED << leader, term, committed_cmds, applied_cmds, proposal_status, pending_proposals >>

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas, cmd \in pending_proposals[r] : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in pending_proposals[r] : ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas, cmd \in committed_cmds : ProcessCommitMsg(r, cmd)
    \/ \E l \in Replicas : LeaderChange(l)
    \/ \E r \in Replicas : LeaderRecovery(r)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====