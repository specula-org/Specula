---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Server, Command, Key, ProposeId

ASSUME IsFiniteSet(Server)
ASSUME IsFiniteSet(Command)
ASSUME IsFiniteSet(Key)
ASSUME IsFiniteSet(ProposeId)

\* -- Helper Functions --

\* Returns the command record for a given proposal ID.
GetCommand(id) == CHOOSE cmd \in Command: cmd.id = id

\* Returns the key for a given command.
GetKey(cmd) == cmd.key

\* Defines the size of a simple majority quorum.
Quorum(S) == (Cardinality(S) \div 2) + 1

\* Defines the size of a recovery quorum.
RecoverQuorum(S) == (Quorum(S) \div 2) + 1

\* Defines the size of a super quorum for fast-path decisions.
SuperQuorum(S) == (Cardinality(S) - Quorum(S)) + RecoverQuorum(S)

\* -- State Variables --
VARIABLES
    \* The current leader server.
    leader,
    \* Each server's speculative pool of proposed commands.
    spec_pool,
    \* Each server's uncommitted pool (meaningful only for the leader).
    uncommitted_pool,
    \* The globally agreed-upon log of committed command IDs.
    committed_log,
    \* Tracks each server's conflict check result for a proposal.
    proposal_status,
    \* Client's set of active proposals awaiting a response.
    active_proposals,
    \* Client's knowledge of commands confirmed via the fast path.
    client_known_speculated,
    \* Client's knowledge of commands confirmed via the slow path (fully committed).
    client_known_committed

vars == << leader, spec_pool, uncommitted_pool, committed_log, proposal_status,
           active_proposals, client_known_speculated, client_known_committed >>

\* -- System Specification --

TypeOK ==
    /\ leader \in Server
    /\ spec_pool \in [Server -> SUBSET ProposeId]
    /\ uncommitted_pool \in [Server -> SUBSET ProposeId]
    /\ committed_log \in Seq(ProposeId)
    /\ proposal_status \in [Server -> [ProposeId -> {"Pending", "NoConflict", "Conflict"}]]
    /\ active_proposals \subseteq ProposeId
    /\ client_known_speculated \subseteq ProposeId
    /\ client_known_committed \subseteq ProposeId

Init ==
    /\ \E l \in Server: leader = l
    /\ spec_pool = [s \in Server |-> {}]
    /\ uncommitted_pool = [s \in Server |-> {}]
    /\ committed_log = <<>>
    /\ proposal_status = [s \in Server |-> [id \in ProposeId |-> "Pending"]]
    /\ active_proposals = {}
    /\ client_known_speculated = {}
    /\ client_known_committed = {}

\* A client proposes a new command, broadcasting it to all servers.
Propose(cmd) ==
    /\ cmd.id \notin active_proposals \cup client_known_speculated \cup client_known_committed
    /\ active_proposals' = active_proposals \cup {cmd.id}
    /\ spec_pool' = [s \in Server |-> spec_pool[s] \cup {cmd.id}]
    /\ proposal_status' = [s \in Server |->
        [id \in ProposeId |-> IF id = cmd.id THEN "Pending" ELSE proposal_status[s][id]]]
    /\ UNCHANGED <<leader, uncommitted_pool, committed_log,
                   client_known_speculated, client_known_committed>>

\* The leader processes a proposed command, checking for conflicts.
ProcessProposeLeader(r, cmd) ==
    /\ r = leader
    /\ cmd.id \in spec_pool[r]
    /\ proposal_status[r][cmd.id] = "Pending"
    /\ LET
        AllPoolCmds == {GetCommand(id) : id \in spec_pool[r] \cup uncommitted_pool[r]}
        ConflictingCmds == {c \in AllPoolCmds : GetKey(c) = GetKey(cmd)}
       IN
        IF Cardinality(ConflictingCmds) = 1 THEN \* No conflict
            /\ spec_pool' = [s \in Server |-> IF s = r THEN spec_pool[s] \ {cmd.id} ELSE spec_pool[s]]
            /\ uncommitted_pool' = [s \in Server |-> IF s = r THEN uncommitted_pool[s] \cup {cmd.id} ELSE uncommitted_pool[s]]
            /\ proposal_status' = [s \in Server |->
                [id \in ProposeId |-> IF s = r /\ id = cmd.id THEN "NoConflict" ELSE proposal_status[s][id]]]
        ELSE \* Conflict detected
            /\ proposal_status' = [s \in Server |->
                [id \in ProposeId |-> IF s = r /\ id = cmd.id THEN "Conflict" ELSE proposal_status[s][id]]]
            /\ UNCHANGED <<spec_pool, uncommitted_pool>>
    /\ UNCHANGED <<leader, committed_log, active_proposals,
                   client_known_speculated, client_known_committed>>

\* A non-leader (follower) processes a proposed command.
ProcessProposeNonLeader(r, cmd) ==
    /\ r # leader
    /\ cmd.id \in spec_pool[r]
    /\ proposal_status[r][cmd.id] = "Pending"
    /\ LET
        SpecPoolCmds == {GetCommand(id) : id \in spec_pool[r]}
        ConflictingCmds == {c \in SpecPoolCmds : GetKey(c) = GetKey(cmd)}
       IN
        IF Cardinality(ConflictingCmds) = 1 THEN \* No conflict
            /\ proposal_status' = [s \in Server |->
                [id \in ProposeId |-> IF s = r /\ id = cmd.id THEN "NoConflict" ELSE proposal_status[s][id]]]
        ELSE \* Conflict detected
            /\ proposal_status' = [s \in Server |->
                [id \in ProposeId |-> IF s = r /\ id = cmd.id THEN "Conflict" ELSE proposal_status[s][id]]]
    /\ UNCHANGED <<leader, spec_pool, uncommitted_pool, committed_log, active_proposals,
                   client_known_speculated, client_known_committed>>

\* The client checks if it has enough non-conflicting responses for a fast-path decision.
ClientCheckFastPath(cmd) ==
    /\ cmd.id \in active_proposals
    /\ LET
        NoConflictServers == {s \in Server | proposal_status[s][cmd.id] = "NoConflict"}
        LeaderConflict == proposal_status[leader][cmd.id] = "Conflict"
       IN
        IF Cardinality(NoConflictServers) >= SuperQuorum(Server) /\ ~LeaderConflict THEN
            /\ client_known_speculated' = client_known_speculated \cup {cmd.id}
            /\ active_proposals' = active_proposals \ {cmd.id}
            /\ UNCHANGED <<leader, spec_pool, uncommitted_pool, committed_log, proposal_status, client_known_committed>>
        ELSE
            UNCHANGED vars

\* The client checks if a command has been committed for a slow-path decision.
ClientCheckSlowPath(cmd) ==
    /\ cmd.id \in active_proposals
    /\ \E i \in 1..Len(committed_log): committed_log[i] = cmd.id
    /\ client_known_committed' = client_known_committed \cup {cmd.id}
    /\ active_proposals' = active_proposals \ {cmd.id}
    /\ UNCHANGED <<leader, spec_pool, uncommitted_pool, committed_log, proposal_status, client_known_speculated>>

\* The backend consensus protocol commits a command from the leader's uncommitted pool.
Commit(cmd) ==
    /\ cmd.id \in uncommitted_pool[leader]
    /\ \A i \in 1..Len(committed_log): committed_log[i] # cmd.id
    /\ committed_log' = Append(committed_log, cmd.id)
    /\ UNCHANGED <<leader, spec_pool, uncommitted_pool, proposal_status,
                   active_proposals, client_known_speculated, client_known_committed>>

\* A server processes a commit message, performing garbage collection.
ProcessCommitMsg(r, cmd) ==
    /\ \E i \in 1..Len(committed_log): committed_log[i] = cmd.id
    /\ cmd.id \in spec_pool[r]
    /\ spec_pool' = [s \in Server |-> IF s = r THEN spec_pool[s] \ {cmd.id} ELSE spec_pool[s]]
    /\ uncommitted_pool' = [s \in Server |-> IF s = r THEN uncommitted_pool[s] \ {cmd.id} ELSE uncommitted_pool[s]]
    /\ UNCHANGED <<leader, committed_log, proposal_status, active_proposals,
                   client_known_speculated, client_known_committed>>

\* The backend consensus protocol elects a new leader, which recovers its state.
LeaderChange(l) ==
    /\ l \in Server
    /\ l # leader
    /\ \E Q \in SUBSET Server:
        /\ Cardinality(Q) >= Quorum(Server)
        /\ LET
            CollectedPoolsBag == UNION { AsBag(spec_pool[s]) : s \in Q }
            RecoveredCmds == { id \in DOMAIN CollectedPoolsBag | BagCount(id, CollectedPoolsBag) >= RecoverQuorum(Server) }
           IN
            /\ leader' = l
            /\ uncommitted_pool' = [s \in Server |-> IF s = l THEN RecoveredCmds ELSE uncommitted_pool[s]]
            /\ spec_pool' = [s \in Server |-> IF s = l THEN BagToSet(CollectedPoolsBag) ELSE spec_pool[s]]
    /\ UNCHANGED <<committed_log, proposal_status, active_proposals,
                   client_known_speculated, client_known_committed>>

Next ==
    \/ \E cmd \in Command: Propose(cmd)
    \/ \E r \in Server, cmd \in Command: ProcessProposeLeader(r, GetCommand(cmd.id))
    \/ \E r \in Server, cmd \in Command: ProcessProposeNonLeader(r, GetCommand(cmd.id))
    \/ \E cmd \in Command: ClientCheckFastPath(cmd)
    \/ \E cmd \in Command: ClientCheckSlowPath(cmd)
    \/ \E cmd \in Command: Commit(cmd)
    \/ \E r \in Server, cmd \in Command: ProcessCommitMsg(r, GetCommand(cmd.id))
    \/ \E l \in Server: LeaderChange(l)

Spec == Init /\ [][Next]_vars

====