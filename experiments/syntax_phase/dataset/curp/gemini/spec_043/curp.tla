---- MODULE curp ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS
    Replicas,
    Commands,
    Keys,
    Nil

ASSUME
    /\ IsFiniteSet(Replicas)
    /\ IsFiniteSet(Commands)
    /\ IsFiniteSet(Keys)
    /\ Nil \notin Replicas
    /\ \A cmd \in Commands : cmd["type"] = "cmd"
    /\ \A cmd \in Commands : cmd["key"] \in Keys

Key(cmd) == cmd["key"]

QuorumSize == (Cardinality(Replicas) \div 2) + 1
RecoverQuorumSize == (QuorumSize \div 2) + 1
SuperQuorumSize == (Cardinality(Replicas) - QuorumSize) + RecoverQuorumSize

Conflicts(cmd, cmdSet) ==
    \E c \in cmdSet : Key(cmd) = Key(c)

VARIABLES
    leader,
    speculative_pool,
    uncommitted_pool,
    committed_pool,
    client_requests,
    fast_path_responses,
    slow_path_responses

vars == <<
    leader,
    speculative_pool,
    uncommitted_pool,
    committed_pool,
    client_requests,
    fast_path_responses,
    slow_path_responses
>>

TypeOK ==
    /\ leader \in Replicas \cup {Nil}
    /\ speculative_pool \in [Replicas -> SUBSET Commands]
    /\ uncommitted_pool \in [Replicas -> SUBSET Commands]
    /\ committed_pool \subseteq Commands
    /\ client_requests \subseteq Commands
    /\ IsABag(fast_path_responses)
    /\ IsABag(slow_path_responses)

Init ==
    /\ leader \in Replicas \cup {Nil}
    /\ speculative_pool = [r \in Replicas |-> {}]
    /\ uncommitted_pool = [r \in Replicas |-> {}]
    /\ committed_pool = {}
    /\ client_requests = {}
    /\ fast_path_responses = EmptyBag
    /\ slow_path_responses = EmptyBag

ClientPropose(cmd) ==
    /\ cmd \in Commands
    /\ cmd \notin client_requests
    /\ \A r \in Replicas : cmd \notin speculative_pool[r]
    /\ \A r \in Replicas : cmd \notin uncommitted_pool[r]
    /\ cmd \notin committed_pool
    /\ client_requests' = client_requests \cup {cmd}
    /\ UNCHANGED <<
        leader,
        speculative_pool,
        uncommitted_pool,
        committed_pool,
        fast_path_responses,
        slow_path_responses
    >>

ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ cmd \in client_requests
    /\ speculative_pool' = [speculative_pool EXCEPT ![r] = @ \cup {cmd}]
    /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \cup {cmd}]
    /\ client_requests' = client_requests \setminus {cmd}
    /\ UNCHANGED <<
        leader,
        committed_pool,
        fast_path_responses,
        slow_path_responses
    >>

ProcessProposeNonLeader(r, cmd) ==
    LET spec_conflict == Conflicts(cmd, speculative_pool[r]) IN
        /\ r \in Replicas
        /\ r # leader
        /\ cmd \in client_requests
        /\ speculative_pool' =
            IF \lnot spec_conflict THEN
                [speculative_pool EXCEPT ![r] = @ \cup {cmd}]
            ELSE
                speculative_pool
        /\ UNCHANGED <<
            leader,
            uncommitted_pool,
            committed_pool,
            client_requests,
            fast_path_responses,
            slow_path_responses
        >>

FastPathCommit ==
    /\ leader # Nil
    /\ \E cmd \in Commands:
        /\ cmd \in speculative_pool[leader]
        /\ cmd \notin committed_pool
        /\ LET acks == {r \in Replicas : cmd \in speculative_pool[r]} IN
            /\ Cardinality(acks) >= SuperQuorumSize
            /\ \A replica \in acks : \lnot Conflicts(cmd, speculative_pool[replica] \setminus {cmd})
            /\ committed_pool' = committed_pool \cup {cmd}
            /\ fast_path_responses' = fast_path_responses (+) Bag({cmd})
            /\ UNCHANGED <<
                leader,
                speculative_pool,
                uncommitted_pool,
                client_requests,
                slow_path_responses
               >>

BackendCommit ==
    /\ leader # Nil
    /\ \E chosen_cmd \in {c \in uncommitted_pool[leader] : c \notin committed_pool}:
        /\ committed_pool' = committed_pool \cup {chosen_cmd}
        /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![leader] = @ \setminus {chosen_cmd}]
        /\ slow_path_responses' = slow_path_responses (+) Bag({chosen_cmd})
        /\ UNCHANGED <<leader, speculative_pool, client_requests, fast_path_responses>>

ProcessCommitMsg(r, cmd) ==
    /\ r \in Replicas
    /\ cmd \in committed_pool
    /\ cmd \in speculative_pool[r]
    /\ speculative_pool' = [speculative_pool EXCEPT ![r] = @ \setminus {cmd}]
    /\ UNCHANGED <<
        leader,
        uncommitted_pool,
        committed_pool,
        client_requests,
        fast_path_responses,
        slow_path_responses
    >>

LeaderChange(new_leader) ==
    /\ new_leader \in Replicas
    /\ leader' = new_leader
    /\ \E quorum \subseteq Replicas:
        LET
            all_cmds_in_quorum_pools == UNION {speculative_pool[q] : q \in quorum}
            recovered_cmds ==
                {c \in all_cmds_in_quorum_pools :
                    Cardinality({q \in quorum : c \in speculative_pool[q]}) >= RecoverQuorumSize}
        IN
            /\ Cardinality(quorum) >= RecoverQuorumSize
            /\ speculative_pool' = [speculative_pool EXCEPT ![new_leader] = recovered_cmds]
            /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![new_leader] = recovered_cmds]
    /\ UNCHANGED <<
        committed_pool,
        client_requests,
        fast_path_responses,
        slow_path_responses
    >>

Next ==
    \/ \E cmd \in Commands : ClientPropose(cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in Commands : ProcessProposeNonLeader(r, cmd)
    \/ FastPathCommit
    \/ BackendCommit
    \/ \E r \in Replicas, cmd \in Commands : ProcessCommitMsg(r, cmd)
    \/ \E l \in Replicas : LeaderChange(l)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====
