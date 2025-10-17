---- MODULE curp ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Server,     \* The set of server nodes
    Command,    \* The set of commands clients can propose
    ProposeId,  \* A set of unique identifiers for proposals
    Value,      \* The set of possible results from command execution
    Nil         \* A special value indicating no result yet

ASSUME Nil \notin Value
ASSUME Cardinality(Server) >= 1

VARIABLES
    leader,         \* The current leader node
    clientState,    \* The state of each client proposal
    speculativePool,\* Commands speculatively stored on each server
    log,            \* The replicated, committed log on each server
    commitIndex     \* The index of the highest log entry known to be committed

vars == <<leader, clientState, speculativePool, log, commitIndex>>

\* Helper operators for quorum calculations
Quorum(S) == Cardinality(S) \div 2 + 1
RecoverQuorum(S) == Quorum(S) \div 2 + 1
SuperQuorum(S) == (Cardinality(S) - Quorum(S)) + RecoverQuorum(S)

\* Uninterpreted functions to model application logic
Conflicts(cmd, pool) == CHOOSE b \in BOOLEAN : TRUE
SpeculativeExecute(cmd) == CHOOSE v \in Value : TRUE
AfterSyncExecute(cmd) == CHOOSE v \in Value : TRUE

TypeOK ==
    /\ leader \in Server
    /\ clientState \in [ProposeId -> [
        cmd: Command,
        status: {"requesting", "speculating", "syncing", "done"},
        er: Value \cup {Nil},
        asr: Value \cup {Nil},
        conflict: BOOLEAN,
        records: SUBSET Server
    ]]
    /\ speculativePool \in [Server -> SUBSET [id: ProposeId, cmd: Command]]
    /\ log \in [Server -> Seq([id: ProposeId, cmd: Command])]
    /\ commitIndex \in [Server -> Nat]

Init ==
    /\ leader \in Server
    /\ clientState = [id \in ProposeId |-> [
        cmd |-> (CHOOSE c \in Command : TRUE),
        status |-> "requesting",
        er |-> Nil,
        asr |-> Nil,
        conflict |-> FALSE,
        records |-> {}
    ]]
    /\ speculativePool = [s \in Server |-> {}]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]

\* A client submits a new command proposal.
ClientPropose(id) ==
    /\ clientState[id].status = "requesting"
    /\ clientState' = [clientState EXCEPT ![id].status = "speculating"]
    /\ UNCHANGED <<leader, speculativePool, log, commitIndex>>

\* The leader receives a proposal, speculatively executes it, and adds it to its pool.
LeaderReceivePropose(id) ==
    LET req == clientState[id]
    IN /\ req.status = "speculating"
       /\ \lnot \exists r \in speculativePool[leader] : r.id = id
       /\ LET pool == speculativePool[leader]
              cmd == req.cmd
              hasConflict == Conflicts(cmd, {p.cmd | p \in pool})
          IN clientState' = [clientState EXCEPT ![id].er = SpeculativeExecute(cmd),
                                                 ![id].conflict = hasConflict,
                                                 ![id].records = @ \cup {leader}]
       /\ speculativePool' = [speculativePool EXCEPT ![leader] = @ \cup {[id |-> id, cmd |-> req.cmd]}]
       /\ UNCHANGED <<leader, log, commitIndex>>

\* A follower receives a record request for a command.
FollowerRecord(follower, id) ==
    /\ follower # leader
    /\ clientState[id].status \in {"speculating", "syncing"}
    /\ follower \notin clientState[id].records
    /\ \lnot \exists r \in speculativePool[follower] : r.id = id
    /\ clientState' = [clientState EXCEPT ![id].records = @ \cup {follower}]
    /\ speculativePool' = [speculativePool EXCEPT ![follower] = @ \cup {[id |-> id, cmd |-> clientState[id].cmd]}]
    /\ UNCHANGED <<leader, log, commitIndex>>

\* The client achieves a superquorum of records without conflict, deciding on the fast path.
ClientDecideFastPath(id) ==
    LET st == clientState[id]
    IN /\ st.status = "speculating"
       /\ st.conflict = FALSE
       /\ Cardinality(st.records) >= SuperQuorum(Server)
       /\ clientState' = [clientState EXCEPT ![id].status = "done"]
       /\ UNCHANGED <<leader, speculativePool, log, commitIndex>>

\* The leader commits a command from its speculative pool to its log (abstracted Raft action).
LeaderCommit(id) ==
    /\ \exists r \in speculativePool[leader] : r.id = id
    /\ LET entryToCommit == CHOOSE r \in speculativePool[leader] : r.id = id
       IN /\ log' = [log EXCEPT ![leader] = Append(@, entryToCommit)]
          /\ speculativePool' = [speculativePool EXCEPT ![leader] = @ \ {entryToCommit}]
          /\ IF clientState[id].conflict = TRUE \/ Cardinality(clientState[id].records) < SuperQuorum(Server)
             THEN clientState' = [clientState EXCEPT ![id].status = "syncing"]
             ELSE UNCHANGED clientState
    /\ UNCHANGED <<leader, commitIndex>>

\* A follower replicates a log entry from the leader (abstracted Raft action).
FollowerReplicate(follower, index) ==
    /\ follower # leader
    /\ Len(log[follower]) = index - 1
    /\ Len(log[leader]) >= index
    /\ LET entryToReplicate == log[leader][index]
       IN /\ log' = [log EXCEPT ![follower] = Append(@, entryToReplicate)]
          /\ speculativePool' = [speculativePool EXCEPT ![follower] = {r \in @ | r.id # entryToReplicate.id}]
    /\ UNCHANGED <<leader, clientState, commitIndex>>

\* A server applies a committed log entry. The leader generates the After-Sync Result.
ServerApply(server) ==
    /\ LET newCommitIndex == commitIndex[server] + 1
    IN /\ newCommitIndex <= Len(log[server])
       /\ commitIndex' = [commitIndex EXCEPT ![server] = newCommitIndex]
       /\ IF server = leader
          THEN LET entry == log[server][newCommitIndex]
               IN clientState' = [clientState EXCEPT ![entry.id].asr = AfterSyncExecute(entry.cmd)]
          ELSE UNCHANGED clientState
    /\ UNCHANGED <<leader, speculativePool, log>>

\* The client receives the After-Sync Result and decides on the slow path.
ClientDecideSlowPath(id) ==
    LET st == clientState[id]
    IN /\ st.status = "syncing"
       /\ st.asr # Nil
       /\ clientState' = [clientState EXCEPT ![id].status = "done"]
       /\ UNCHANGED <<leader, speculativePool, log, commitIndex>>

\* The leader changes non-deterministically (abstracted Raft leader election).
LeaderChange ==
    /\ leader' \in Server
    /\ UNCHANGED <<clientState, speculativePool, log, commitIndex>>

Next ==
    \/ \exists id \in ProposeId : ClientPropose(id)
    \/ \exists id \in ProposeId : LeaderReceivePropose(id)
    \/ \exists f \in Server, id \in ProposeId : FollowerRecord(f, id)
    \/ \exists id \in ProposeId : ClientDecideFastPath(id)
    \/ \exists id \in ProposeId : LeaderCommit(id)
    \/ \exists f \in Server, i \in 1..Len(log[leader]) : FollowerReplicate(f, i)
    \/ \exists s \in Server : ServerApply(s)
    \/ \exists id \in ProposeId : ClientDecideSlowPath(id)
    \/ LeaderChange

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* A proposed command is eventually decided.
Liveness == \A id \in ProposeId : <> (clientState[id].status = "done")

====