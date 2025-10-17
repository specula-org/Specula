---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, Command, Key
ASSUME IsFiniteSet(Server) /\ Server /= {}
ASSUME IsFiniteSet(Command) /\ Command /= {}
ASSUME IsFiniteSet(Key) /\ Key /= {}

CONSTANT GetCommandKey
ASSUME GetCommandKey \in [Command -> Key]

N == Cardinality(Server)

Quorum(n) == (n \div 2) + 1
RecoverQuorum(n) == (Quorum(n) \div 2) + 1
SuperQuorum(n) == (n - Quorum(n)) + RecoverQuorum(n)

VARIABLES
    leader,
    spec_pool,
    uncommitted_pool,
    committed,
    proposed_cmds,
    processed_proposals,
    client_responses,
    fast_path_possible

vars == <<leader, spec_pool, uncommitted_pool, committed, proposed_cmds, processed_proposals, client_responses, fast_path_possible>>

Init ==
    /\ \E l \in Server : leader = l
    /\ spec_pool = [r \in Server |-> {}]
    /\ uncommitted_pool = [r \in Server |-> {}]
    /\ committed = {}
    /\ proposed_cmds = {}
    /\ processed_proposals = [r \in Server |-> {}]
    /\ client_responses = [cmd \in Command |-> {}]
    /\ fast_path_possible = [cmd \in Command |-> FALSE]

Keys(CmdSet) == { GetCommandKey(c) : c \in CmdSet }

Propose(cmd) ==
    /\ cmd \in Command
    /\ cmd \notin proposed_cmds
    /\ proposed_cmds' = proposed_cmds \cup {cmd}
    /\ spec_pool' = [r \in Server |-> spec_pool[r] \cup {cmd}]
    /\ UNCHANGED <<leader, uncommitted_pool, committed, processed_proposals, client_responses, fast_path_possible>>

ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ cmd \in spec_pool[r]
    /\ cmd \notin processed_proposals[r]
    /\ LET
        conflict_spec == GetCommandKey(cmd) \in Keys(spec_pool[r] \ {cmd})
        conflict_uncommitted == GetCommandKey(cmd) \in Keys(uncommitted_pool[r])
        conflict == conflict_spec \/ conflict_uncommitted
       IN
        /\ IF ~conflict
           THEN /\ fast_path_possible' = [fast_path_possible EXCEPT ![cmd] = TRUE]
                /\ client_responses' = [client_responses EXCEPT ![cmd] = @ \cup {r}]
           ELSE /\ fast_path_possible' = [fast_path_possible EXCEPT ![cmd] = FALSE]
                /\ UNCHANGED client_responses
    /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \ {cmd}]
    /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \cup {cmd}]
    /\ processed_proposals' = [processed_proposals EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<leader, committed, proposed_cmds>>

ProcessProposeNonLeader(r, cmd) ==
    /\ r /= leader
    /\ cmd \in spec_pool[r]
    /\ cmd \notin processed_proposals[r]
    /\ LET
        conflict == GetCommandKey(cmd) \in Keys(spec_pool[r] \ {cmd})
       IN
        /\ IF ~conflict
           THEN client_responses' = [client_responses EXCEPT ![cmd] = @ \cup {r}]
           ELSE UNCHANGED client_responses
    /\ processed_proposals' = [processed_proposals EXCEPT ![r] = @ \cup {cmd}]
    /\ UNCHANGED <<leader, spec_pool, uncommitted_pool, committed, proposed_cmds, fast_path_possible>>

ReplicateLog(follower, cmd) ==
    /\ follower /= leader
    /\ cmd \in uncommitted_pool[leader]
    /\ cmd \notin uncommitted_pool[follower]
    /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![follower] = @ \cup {cmd}]
    /\ UNCHANGED <<leader, spec_pool, committed, proposed_cmds, processed_proposals, client_responses, fast_path_possible>>

Commit(cmd) ==
    /\ cmd \notin committed
    /\ \/ (* Fast Path *)
       /\ fast_path_possible[cmd]
       /\ Cardinality(client_responses[cmd]) >= SuperQuorum(N)
    \/ (* Slow Path *)
       /\ cmd \in uncommitted_pool[leader]
       /\ Cardinality({r \in Server : cmd \in uncommitted_pool[r]}) >= Quorum(N)
    /\ committed' = committed \cup {cmd}
    /\ UNCHANGED <<leader, spec_pool, uncommitted_pool, proposed_cmds, processed_proposals, client_responses, fast_path_possible>>

ProcessCommitMsg(r, cmd) ==
    /\ r \in Server
    /\ cmd \in committed
    /\ (cmd \in spec_pool[r] \/ cmd \in uncommitted_pool[r])
    /\ spec_pool' = [spec_pool EXCEPT ![r] = @ \ {cmd}]
    /\ uncommitted_pool' = [uncommitted_pool EXCEPT ![r] = @ \ {cmd}]
    /\ UNCHANGED <<leader, committed, proposed_cmds, processed_proposals, client_responses, fast_path_possible>>

LeaderChange(l) ==
    /\ l \in Server
    /\ l /= leader
    /\ \E QuorumSet \subseteq Server:
        /\ Cardinality(QuorumSet) = Quorum(N)
        /\ LET
            CollectedPoolsBag == BagUnion({ SetToBag(spec_pool[s]) : s \in QuorumSet })
            RecoveredCmds == { cmd \in Command : BagMultiplicity(cmd, CollectedPoolsBag) >= RecoverQuorum(N) }
           IN
            /\ leader' = l
            /\ uncommitted_pool' = [r \in Server |-> IF r = l THEN RecoveredCmds ELSE {}]
            /\ spec_pool' = [r \in Server |-> IF r = l THEN spec_pool[r] \cup RecoveredCmds ELSE spec_pool[r]]
            /\ processed_proposals' = [r \in Server |-> IF r = l THEN {} ELSE processed_proposals[r]]
    /\ UNCHANGED <<committed, proposed_cmds, client_responses, fast_path_possible>>

Next ==
    \/ \E cmd \in Command : Propose(cmd)
    \/ \E r \in Server, cmd \in Command : ProcessProposeLeader(r, cmd)
    \/ \E r \in Server, cmd \in Command : ProcessProposeNonLeader(r, cmd)
    \/ \E follower \in Server, cmd \in Command : ReplicateLog(follower, cmd)
    \/ \E cmd \in Command : Commit(cmd)
    \/ \E r \in Server, cmd \in Command : ProcessCommitMsg(r, cmd)
    \/ \E l \in Server : LeaderChange(l)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====