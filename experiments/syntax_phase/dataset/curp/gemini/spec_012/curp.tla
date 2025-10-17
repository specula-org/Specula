---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, Key, Value, ProposeId

VARIABLES leader, spec_pool, uncommitted_pool, committed_log, pending_proposals, processed_proposals

vars == <<leader, spec_pool, uncommitted_pool, committed_log, pending_proposals, processed_proposals>>

Command == [id: ProposeId, key: Key, val: Value]

AsSet(seq) == {seq[i] : i \in DOMAIN seq}

Quorum(S) == Cardinality(S) \div 2 + 1
FaultTolerance(S) == Cardinality(S) - Quorum(S)
RecoverQuorum(S) == Quorum(S) \div 2 + 1
SuperQuorum(S) == FaultTolerance(S) + RecoverQuorum(S)

Init ==
    /\ leader \in Server
    /\ spec_pool = [s \in Server |-> {}]
    /\ uncommitted_pool = [s \in Server |-> {}]
    /\ committed_log = <<>>
    /\ pending_proposals = {}
    /\ processed_proposals = [s \in Server |-> {}]

Propose(cmd) ==
    /\ cmd \notin pending_proposals
    /\ \A s \in Server : cmd \notin processed_proposals[s]
    /\ pending_proposals' = pending_proposals \cup {cmd}
    /\ UNCHANGED <<leader, spec_pool, uncommitted_pool, committed_log, processed_proposals>>

ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ cmd \in pending_proposals
    /\ cmd \notin processed_proposals[r]
    /\ LET conflict_sp == \E c \in spec_pool[r] : c.key = cmd.key
           conflict_ucp == \E c \in uncommitted_pool[r] : c.key = cmd.key
           conflict == conflict_sp \/ conflict_ucp
       IN /\ spec_pool' = [spec_pool EXCEPT ![r] = IF conflict THEN @ ELSE @ \cup {cmd}]
          /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \cup {cmd}]
          /\ processed_proposals' = [processed_proposals EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<leader, committed_log, pending_proposals>>

ProcessProposeNonLeader(r, cmd) ==
    /\ r /= leader
    /\ cmd \in pending_proposals
    /\ cmd \notin processed_proposals[r]
    /\ LET conflict_sp == \E c \in spec_pool[r] : c.key = cmd.key
       IN /\ spec_pool' = [spec_pool EXCEPT ![r] = IF conflict_sp THEN @ ELSE @ \cup {cmd}]
          /\ processed_proposals' = [processed_proposals EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<leader, uncommitted_pool, committed_log, pending_proposals>>

Commit(cmd) ==
    /\ cmd \in uncommitted_pool[leader]
    /\ committed_log' = Append(committed_log, cmd)
    /\ uncommitted_pool' = [s \in Server |-> {c \in uncommitted_pool[s] | c.id /= cmd.id}]
    /\ UNCHANGED <<leader, spec_pool, pending_proposals, processed_proposals>>

ProcessCommitMsg(r, cmd) ==
    /\ r \in Server
    /\ cmd \in AsSet(committed_log)
    /\ \E c_in_sp \in spec_pool[r] : c_in_sp.key = cmd.key
    /\ spec_pool' = [spec_pool EXCEPT ![r] = {c \in @ | c.key /= cmd.key}]
    /\ UNCHANGED <<leader, uncommitted_pool, committed_log, pending_proposals, processed_proposals>>

LeaderChange(new_leader) ==
    /\ new_leader \in Server
    /\ new_leader /= leader
    /\ \E quorum_servers \subseteq Server:
        /\ Cardinality(quorum_servers) >= RecoverQuorum(Server)
        /\ LET recovered_cmds == UNION {spec_pool[s] : s \in quorum_servers}
           IN /\ leader' = new_leader
              /\ spec_pool' = [spec_pool EXCEPT ![new_leader] = recovered_cmds]
              /\ uncommitted_pool' = [s \in Server |-> IF s = new_leader THEN recovered_cmds ELSE {}]
    /\ UNCHANGED <<committed_log, pending_proposals, processed_proposals>>

Next ==
    \/ \E cmd \in Command : Propose(cmd)
    \/ \E r \in Server, cmd \in Command : ProcessProposeLeader(r, cmd)
    \/ \E r \in Server, cmd \in Command : ProcessProposeNonLeader(r, cmd)
    \/ \E cmd \in Command : Commit(cmd)
    \/ \E r \in Server, cmd \in Command : ProcessCommitMsg(r, cmd)
    \/ \E l \in Server : LeaderChange(l)

Spec == Init /\ [][Next]_vars

====