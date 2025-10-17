---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets

CONSTANTS Replicas, Commands, Key, GetKey

ASSUME IsFiniteSet(Replicas) /\ Replicas # {}
ASSUME IsFiniteSet(Commands)
ASSUME IsFiniteSet(Key)
ASSUME \A c \in Commands: GetKey[c] \in Key

N == Cardinality(Replicas)
Quorum == (N \div 2) + 1
RecoverQuorum == (Quorum \div 2) + 1

Keys(cmds) == { GetKey[c] : c \in cmds }
AsSet(s) == { s[i] : i \in DOMAIN s }

VARIABLES
    leader,
    term,
    speculative_pool,
    uncommitted_pool,
    committed_cmds,
    client_proposals

vars == << leader, term, speculative_pool, uncommitted_pool, committed_cmds, client_proposals >>

TypeOK ==
    /\ leader \in Replicas
    /\ term \in Nat
    /\ speculative_pool \in [Replicas -> SUBSET Commands]
    /\ uncommitted_pool \in [Replicas -> Seq(Commands)]
    /\ committed_cmds \subseteq Commands
    /\ client_proposals \subseteq Commands

Init ==
    /\ term = 1
    /\ \E l \in Replicas: leader = l
    /\ speculative_pool = [r \in Replicas |-> {}]
    /\ uncommitted_pool = [r \in Replicas |-> <<>>]
    /\ committed_cmds = {}
    /\ client_proposals = {}

Propose(cmd) ==
    /\ cmd \in Commands
    /\ cmd \notin client_proposals
    /\ \A r \in Replicas: cmd \notin speculative_pool[r]
    /\ \A r \in Replicas: cmd \notin AsSet(uncommitted_pool[r])
    /\ cmd \notin committed_cmds
    /\ client_proposals' = client_proposals \cup {cmd}
    /\ UNCHANGED << leader, term, speculative_pool, uncommitted_pool, committed_cmds >>

ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ cmd \in client_proposals
    /\ LET
        conflict_keys == Keys(speculative_pool[r]) \cup Keys(AsSet(uncommitted_pool[r]))
        has_conflict == GetKey[cmd] \in conflict_keys
       IN
        /\ IF has_conflict THEN
            UNCHANGED speculative_pool
           ELSE
            speculative_pool' = [speculative_pool EXCEPT ![r] = @ \cup {cmd}]
    /\ client_proposals' = client_proposals \ {cmd}
    /\ UNCHANGED << leader, term, uncommitted_pool, committed_cmds >>

ProcessProposeNonLeader(r, cmd) ==
    /\ r \in Replicas
    /\ r /= leader
    /\ cmd \in client_proposals
    /\ LET
        has_conflict == GetKey[cmd] \in Keys(speculative_pool[r])
       IN
        /\ IF has_conflict THEN
            UNCHANGED speculative_pool
           ELSE
            speculative_pool' = [speculative_pool EXCEPT ![r] = @ \cup {cmd}]
    /\ client_proposals' = client_proposals \ {cmd}
    /\ UNCHANGED << leader, term, uncommitted_pool, committed_cmds >>

Commit ==
    /\ \E cmd \in speculative_pool[leader]:
        /\ LET replicas_with_cmd == {r \in Replicas : cmd \in speculative_pool[r]}
           IN Cardinality(replicas_with_cmd) >= Quorum
        /\ \A r \in Replicas: cmd \notin AsSet(uncommitted_pool[r])
        /\ uncommitted_pool' = [r \in Replicas |-> Append(uncommitted_pool[r], cmd)]
        /\ speculative_pool' = [r \in Replicas |-> speculative_pool[r] \ {cmd}]
        /\ UNCHANGED << leader, term, committed_cmds, client_proposals >>

Execute ==
    /\ uncommitted_pool[leader] /= <<>>
    /\ LET cmd == Head(uncommitted_pool[leader])
    /\ committed_cmds' = committed_cmds \cup {cmd}
    /\ uncommitted_pool' = [r \in Replicas |-> Tail(uncommitted_pool[r])]
    /\ UNCHANGED << leader, term, speculative_pool, client_proposals >>

LeaderChange(new_leader) ==
    /\ new_leader \in Replicas
    /\ leader' = new_leader
    /\ term' = term + 1
    /\ \E quorum_replicas \in SUBSET Replicas:
        /\ Cardinality(quorum_replicas) >= RecoverQuorum
        /\ LET
            collected_sps == {speculative_pool[rep] : rep \in quorum_replicas}
            all_collected_cmds == UNION collected_sps
            recovered_cmds == {
                c \in all_collected_cmds :
                Cardinality({rep \in quorum_replicas : c \in speculative_pool[rep]}) >= RecoverQuorum
            }
            current_log_cmds == AsSet(uncommitted_pool[new_leader])
            new_log_cmds == recovered_cmds \ current_log_cmds
            new_log_seq == IF new_log_cmds = {} THEN <<>> ELSE CHOOSE s \in Permutations(new_log_cmds) : TRUE
           IN
            /\ speculative_pool' = [speculative_pool EXCEPT ![new_leader] = @ \cup recovered_cmds]
            /\ uncommitted_pool' = [r \in Replicas |-> uncommitted_pool[r] \o new_log_seq]
    /\ UNCHANGED << committed_cmds, client_proposals >>

Next ==
    \/ \E cmd \in Commands: Propose(cmd)
    \/ \E r \in Replicas, cmd \in client_proposals: ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas, cmd \in client_proposals: ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ Execute
    \/ \E new_leader \in Replicas: LeaderChange(new_leader)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====