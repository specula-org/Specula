---- MODULE etcdraft ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Server,         \* The set of server IDs.
    Value,          \* The set of possible values in the K/V store.
    Key,            \* The set of possible keys in the K/V store.
    Client,         \* The set of client IDs.
    HeartbeatInterval, \* Ticks between heartbeats.
    ElectionTimeout,   \* Base ticks for election timeout.
    PreVoteEnabled     \* Boolean to enable/disable PreVote phase.

ASSUME
    /\ Server = {"s1", "s2", "s3"}
    /\ Value = {"v1", "v2"}
    /\ Key = {"k1", "k2"}
    /\ Client = {"c1"}
    /\ HeartbeatInterval = 1
    /\ ElectionTimeout = 5
    /\ PreVoteEnabled \in {TRUE, FALSE}

\* A special value for uninitialized/null fields.
Null == "Null"

\* Server states from raft.go
States == {"Follower", "PreCandidate", "Candidate", "Leader"}

\* Message types from raftpb/raft.pb.go
MsgTypes == {
    "MsgHup", "MsgBeat", "MsgProp", "MsgApp", "MsgAppResp", "MsgVote", "MsgVoteResp",
    "MsgSnap", "MsgHeartbeat", "MsgHeartbeatResp", "MsgUnreachable", "MsgSnapStatus",
    "MsgCheckQuorum", "MsgTransferLeader", "MsgTimeoutNow", "MsgReadIndex", "MsgReadIndexResp",
    "MsgPreVote", "MsgPreVoteResp"
}

\* A client command to be applied to the state machine.
Command == [type: {"Put"}, key: Key, value: Value, client: Client, reqId: Nat]

\* A log entry contains a command and the term in which it was received.
LogEntry == [term: Nat, command: Command]

\* A message on the network.
Message == [
    type: MsgTypes,
    from: Server \union {Null},
    to: Server,
    term: Nat,
    \* For MsgApp
    prevLogIndex: Nat,
    prevLogTerm: Nat,
    entries: Seq(LogEntry),
    leaderCommit: Nat,
    \* For MsgAppResp / MsgVoteResp
    reject: BOOLEAN,
    matchIndex: Nat,
    \* For MsgVote
    lastLogIndex: Nat,
    lastLogTerm: Nat
]

\* The set of all possible messages.
Messages == UNION {[type: {t}] : t \in MsgTypes}

QuorumSize == (Cardinality(Server) \div 2) + 1

\* Non-deterministically choose a timeout value in the range [E, 2E-1]
RandomizedElectionTimeout(s) == ElectionTimeout + (s.id % ElectionTimeout)

\*=============================================================================
\* State Variables
\*=============================================================================
vars
    \* Per-server state
    state,          \* The role of each server.
    currentTerm,    \* The current term of each server.
    votedFor,       \* Who this server voted for in the current term.
    log,            \* The log on each server.
    commitIndex,    \* Index of highest log entry known to be committed.
    appliedIndex,   \* Index of highest log entry applied to state machine.
    kvStore,        \* The key-value store state for each server.
    timer,          \* Ticks since last message from leader or election start.

    \* Leader-specific state, reinitialized on election.
    nextIndex,      \* For each follower, index of the next log entry to send.
    matchIndex,     \* For each follower, index of highest log entry known to be replicated.

    \* Candidate-specific state
    votesGranted,   \* Set of servers that voted for this candidate.

    \* The network is a set of messages.
    network,

    \* History of client operations for linearizability check.
    history

\*=============================================================================
\* Initial State
\*=============================================================================
Init ==
    /\ state = [s \in Server |-> "Follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Null]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ appliedIndex = [s \in Server |-> 0]
    /\ kvStore = [s \in Server |-> [k \in Key |-> Null]]
    /\ nextIndex = [s \in Server |-> [f \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [f \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ timer = [s \in Server |-> 0]
    /\ network = {}
    /\ history = <<>>

\*=============================================================================
\* Helper Functions
\*=============================================================================
LastLogIndex(s) == Len(log[s])
LastLogTerm(s) == IF LastLogIndex(s) = 0 THEN 0 ELSE log[s][LastLogIndex(s)].term

\* Implements the isUpToDate check from raft.go
IsUpToDate(candidateLastLogTerm, candidateLastLogIndex, myLastLogTerm, myLastLogIndex) ==
    \/ candidateLastLogTerm > myLastLogTerm
    \/ (candidateLastLogTerm = myLastLogTerm /\ candidateLastLogIndex >= myLastLogIndex)

\* Transitions a server to the follower state.
BecomeFollower(s, term, vars) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = Null]
    /\ timer' = [timer EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, network, history>>

\*=============================================================================
\* Actions
\*=============================================================================

\* A server's timer ticks.
Tick(s) ==
    /\ timer' = [timer EXCEPT ![s] = timer[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, network, history>>

\* A follower/candidate times out and starts an election.
Timeout(s) ==
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ timer[s] >= RandomizedElectionTimeout(s)
    /\ IF PreVoteEnabled
       THEN /\ state' = [state EXCEPT ![s] = "PreCandidate"]
            /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
            /\ network' = network \cup
                { [ type |-> "MsgPreVote", from |-> s, to |-> p,
                    term |-> currentTerm[s] + 1,
                    lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s),
                    prevLogIndex |-> 0, entries |-> <<>>, leaderCommit |-> 0,
                    reject |-> FALSE, matchIndex |-> 0 ]
                : p \in Server \ {s} }
            /\ UNCHANGED <<currentTerm, votedFor>>
       ELSE /\ state' = [state EXCEPT ![s] = "Candidate"]
            /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
            /\ votedFor' = [votedFor EXCEPT ![s] = s]
            /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
            /\ network' = network \cup
                { [ type |-> "MsgVote", from |-> s, to |-> p,
                    term |-> currentTerm[s] + 1,
                    lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s),
                    prevLogIndex |-> 0, entries |-> <<>>, leaderCommit |-> 0,
                    reject |-> FALSE, matchIndex |-> 0 ]
                : p \in Server \ {s} }
    /\ timer' = [timer EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, history>>

\* A server receives a message.
Receive(msg) ==
    LET s == msg.to IN
    /\ msg \in network
    /\ LET vars == <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, network, history, timer>> IN
       \/ /\ msg.term > currentTerm[s]
          /\ BecomeFollower(s, msg.term, vars)
       \/ /\ msg.term < currentTerm[s]
          /\ \/ /\ msg.type \in {"MsgApp", "MsgHeartbeat"}
                /\ LET resp == [type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                                term |-> currentTerm[s], reject |-> TRUE,
                                prevLogIndex |-> 0, entries |-> <<>>, leaderCommit |-> 0,
                                matchIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0]
                IN network' = (network \ {msg}) \cup {resp}
             \/ /\ msg.type \in {"MsgVote", "MsgPreVote"}
                /\ LET respType == IF msg.type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp"
                IN LET resp == [type |-> respType, from |-> s, to |-> msg.from,
                                term |-> currentTerm[s], reject |-> TRUE,
                                prevLogIndex |-> 0, entries |-> <<>>, leaderCommit |-> 0,
                                matchIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0]
                IN network' = (network \ {msg}) \cup {resp}
             \/ /\ msg.type \notin {"MsgApp", "MsgHeartbeat", "MsgVote", "MsgPreVote"}
                /\ network' = network \ {msg}
          /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, history, timer>>
       \/ /\ msg.term = currentTerm[s]
          /\ \/ HandleAppendEntries(msg, vars)
             \/ HandleRequestVote(msg, vars)
             \/ HandleAppendEntriesResponse(msg, vars)
             \/ HandleVoteResponse(msg, vars)
             \/ HandleHeartbeat(msg, vars)
             \/ HandleHeartbeatResponse(msg, vars)

\* A server handles an AppendEntries or Heartbeat message.
HandleAppendEntries(msg, vars) ==
    LET s == msg.to IN
    /\ msg.type \in {"MsgApp", "MsgHeartbeat"}
    /\ state[s] \in {"Follower", "PreCandidate", "Candidate"}
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ timer' = [timer EXCEPT ![s] = 0]
    /\ LET logOK ==
            /\ msg.prevLogIndex <= LastLogIndex(s)
            /\ (msg.prevLogIndex = 0 \/ log[s][msg.prevLogIndex].term = msg.prevLogTerm)
       IN IF logOK
          THEN /\ LET newEntries == msg.entries
                 IN LET conflictIndex ==
                        CHOOSE i \in 1..Len(newEntries):
                            msg.prevLogIndex + i > LastLogIndex(s) \/
                            log[s][msg.prevLogIndex + i].term /= newEntries[i].term
                 IN LET newLog ==
                        IF conflictIndex = CHOOSE i: FALSE
                        THEN AppendSeq(log[s], newEntries)
                        ELSE AppendSeq(SubSeq(log[s], 1, msg.prevLogIndex + conflictIndex - 1),
                                       SubSeq(newEntries, conflictIndex, Len(newEntries)))
                 IN log' = [log EXCEPT ![s] = newLog]
                 /\ IF msg.leaderCommit > commitIndex[s]
                    THEN commitIndex' = [commitIndex EXCEPT ![s] = Min({msg.leaderCommit, LastLogIndex(s)})]
                    ELSE UNCHANGED commitIndex
                 /\ LET resp == [type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                                 term |-> currentTerm[s], reject |-> FALSE,
                                 matchIndex |-> LastLogIndex(s),
                                 prevLogIndex |-> 0, entries |-> <<>>, leaderCommit |-> 0,
                                 lastLogIndex |-> 0, lastLogTerm |-> 0]
                 IN network' = (network \ {msg}) \cup {resp}
          ELSE /\ LET resp == [type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                                 term |-> currentTerm[s], reject |-> TRUE,
                                 matchIndex |-> 0,
                                 prevLogIndex |-> 0, entries |-> <<>>, leaderCommit |-> 0,
                                 lastLogIndex |-> 0, lastLogTerm |-> 0]
                 IN network' = (network \ {msg}) \cup {resp}
               /\ UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<currentTerm, votedFor, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, history>>

HandleHeartbeat(msg, vars) == HandleAppendEntries(msg, vars)

\* A server handles a RequestVote or PreVote message.
HandleRequestVote(msg, vars) ==
    LET s == msg.to IN
    /\ msg.type \in {"MsgVote", "MsgPreVote"}
    /\ LET voteGranted ==
            /\ IsUpToDate(msg.lastLogTerm, msg.lastLogIndex, LastLogTerm(s), LastLogIndex(s))
            /\ IF msg.type = "MsgVote"
               THEN votedFor[s] \in {Null, msg.from}
               ELSE TRUE
       IN IF voteGranted
          THEN /\ IF msg.type = "MsgVote"
                  THEN votedFor' = [votedFor EXCEPT ![s] = msg.from]
                  ELSE UNCHANGED votedFor
               /\ LET respType == IF msg.type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp"
               IN LET resp == [type |-> respType, from |-> s, to |-> msg.from,
                               term |-> msg.term, reject |-> FALSE,
                               matchIndex |-> 0, prevLogIndex |-> 0, entries |-> <<>>,
                               leaderCommit |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0]
               IN network' = (network \ {msg}) \cup {resp}
          ELSE /\ LET respType == IF msg.type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp"
                 IN LET resp == [type |-> respType, from |-> s, to |-> msg.from,
                                 term |-> currentTerm[s], reject |-> TRUE,
                                 matchIndex |-> 0, prevLogIndex |-> 0, entries |-> <<>>,
                                 leaderCommit |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0]
                 IN network' = (network \ {msg}) \cup {resp}
               /\ UNCHANGED votedFor
    /\ UNCHANGED <<state, currentTerm, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, history, timer>>

\* A candidate handles a vote response.
HandleVoteResponse(msg, vars) ==
    LET s == msg.to IN
    /\ \/ (state[s] = "Candidate" /\ msg.type = "MsgVoteResp")
       \/ (state[s] = "PreCandidate" /\ msg.type = "MsgPreVoteResp")
    /\ IF msg.reject = FALSE
       THEN /\ votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {msg.from}]
            /\ IF Cardinality(votesGranted'[s]) >= QuorumSize
               THEN IF state[s] = "PreCandidate"
                    THEN /\ state' = [state EXCEPT ![s] = "Candidate"]
                         /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                         /\ votedFor' = [votedFor EXCEPT ![s] = s]
                         /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
                         /\ network' = (network \ {msg}) \cup
                             { [ type |-> "MsgVote", from |-> s, to |-> p,
                                 term |-> currentTerm[s] + 1,
                                 lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s),
                                 prevLogIndex |-> 0, entries |-> <<>>, leaderCommit |-> 0,
                                 reject |-> FALSE, matchIndex |-> 0 ]
                             : p \in Server \ {s} }
                         /\ UNCHANGED <<log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, history, timer>>
                    ELSE /\ state' = [state EXCEPT ![s] = "Leader"]
                         /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(s) + 1]]
                         /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0]]
                         /\ LET noOpEntry == [term |-> currentTerm[s], command |-> Null]
                         IN log' = [log EXCEPT ![s] = Append(log[s], noOpEntry)]
                         /\ network' = (network \ {msg}) \cup
                             { [ type |-> "MsgApp", from |-> s, to |-> p,
                                 term |-> currentTerm[s],
                                 prevLogIndex |-> LastLogIndex(s), prevLogTerm |-> LastLogTerm(s),
                                 entries |-> <<noOpEntry>>, leaderCommit |-> commitIndex[s],
                                 reject |-> FALSE, matchIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0 ]
                             : p \in Server \ {s} }
                         /\ UNCHANGED <<currentTerm, votedFor, commitIndex, appliedIndex, kvStore, votesGranted, history, timer>>
               ELSE /\ network' = network \ {msg}
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, history, timer>>
       ELSE /\ network' = network \ {msg}
            /\ UNCHANGED <<votesGranted, state, currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, history, timer>>

\* A leader handles an AppendEntries response.
HandleAppendEntriesResponse(msg, vars) ==
    LET s == msg.to IN
    /\ state[s] = "Leader"
    /\ msg.type = "MsgAppResp"
    /\ IF msg.reject = FALSE
       THEN /\ matchIndex' = [matchIndex EXCEPT ![s][msg.from] = msg.matchIndex]
            /\ nextIndex' = [nextIndex EXCEPT ![s][msg.from] = msg.matchIndex + 1]
            /\ LET newCommitIndex ==
                   CHOOSE N \in (commitIndex[s]+1)..LastLogIndex(s):
                       /\ log[s][N].term = currentTerm[s]
                       /\ Cardinality({p \in Server: matchIndex'[s][p] >= N} \cup {s}) >= QuorumSize
            IN IF newCommitIndex /= CHOOSE N: FALSE
               THEN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
               ELSE UNCHANGED commitIndex
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][msg.from] = nextIndex[s][msg.from] - 1]
            /\ UNCHANGED <<matchIndex, commitIndex>>
    /\ network' = network \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, appliedIndex, kvStore, votesGranted, history, timer>>

HandleHeartbeatResponse(msg, vars) ==
    LET s == msg.to IN
    /\ state[s] = "Leader"
    /\ msg.type = "MsgHeartbeatResp"
    /\ network' = network \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, history, timer>>

\* A leader sends heartbeats.
LeaderHeartbeat(s) ==
    /\ state[s] = "Leader"
    /\ timer[s] >= HeartbeatInterval
    /\ network' = network \cup
        { [ type |-> "MsgHeartbeat", from |-> s, to |-> p,
            term |-> currentTerm[s],
            prevLogIndex |-> LastLogIndex(p), prevLogTerm |-> LastLogTerm(p),
            entries |-> <<>>, leaderCommit |-> commitIndex[s],
            reject |-> FALSE, matchIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0 ]
        : p \in Server \ {s} }
    /\ timer' = [timer EXCEPT ![s] = 0]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, history>>

\* A leader has new entries to replicate to a follower.
LeaderReplicateLog(s, p) ==
    /\ state[s] = "Leader"
    /\ p /= s
    /\ LastLogIndex(s) >= nextIndex[s][p]
    /\ LET prevIdx == nextIndex[s][p] - 1
    IN LET prevTerm == IF prevIdx > 0 THEN log[s][prevIdx].term ELSE 0
    IN LET entriesToSend == SubSeq(log[s], nextIndex[s][p], LastLogIndex(s))
    IN network' = network \cup
        { [ type |-> "MsgApp", from |-> s, to |-> p,
            term |-> currentTerm[s],
            prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
            entries |-> entriesToSend, leaderCommit |-> commitIndex[s],
            reject |-> FALSE, matchIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0 ] }
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, history, timer>>

\* A client proposes a new command.
ClientRequest(c, k, v, reqId) ==
    \E s \in Server:
        /\ state[s] = "Leader"
        /\ LET cmd == [type |-> "Put", key |-> k, value |-> v, client |-> c, reqId |-> reqId]
        IN log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], command |-> cmd])]
        /\ history' = Append(history, [op |-> "invoke", cmd |-> cmd])
        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, network, timer>>

\* A server applies a committed entry to its state machine.
Apply(s) ==
    /\ commitIndex[s] > appliedIndex[s]
    /\ LET idx == appliedIndex[s] + 1
    IN LET entry == log[s][idx]
    IN LET cmd == entry.command
    IN /\ appliedIndex' = [appliedIndex EXCEPT ![s] = idx]
       /\ IF cmd /= Null
          THEN /\ kvStore' = [kvStore EXCEPT ![s][cmd.key] = cmd.value]
               /\ history' = Append(history, [op |-> "return", cmd |-> cmd])
          ELSE UNCHANGED <<kvStore, history>>
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, votesGranted, network, timer>>

\* A message can be lost.
DropMessage(msg) ==
    /\ msg \in network
    /\ network' = network \ {msg}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex, votesGranted, history, timer>>

\*=============================================================================
\* Next State Relation
\*=============================================================================
Next ==
    \/ \E s \in Server: Tick(s)
    \/ \E s \in Server: Timeout(s)
    \/ \E msg \in network: Receive(msg)
    \/ \E s \in Server: LeaderHeartbeat(s)
    \/ \E s, p \in Server: LeaderReplicateLog(s, p)
    \/ \E c \in Client, k \in Key, v \in Value, reqId \in Nat: ClientRequest(c, k, v, reqId)
    \/ \E s \in Server: Apply(s)
    \/ \E msg \in network: DropMessage(msg)

Spec == Init /\ [][Next]_vars

\*=============================================================================
\* Invariants and Properties
\*=============================================================================
TypeOK ==
    /\ state \in [Server -> States]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \union {Null}]
    /\ \A s \in Server: log[s] \in Seq(LogEntry)
    /\ commitIndex \in [Server -> Nat]
    /\ appliedIndex \in [Server -> Nat]
    /\ kvStore \in [Server -> [Key -> Value \union {Null}]]
    /\ network \subseteq Messages

\* At most one leader per term.
ElectionSafety ==
    \A t \in 1..Max({currentTerm[s] : s \in Server}):
        Cardinality({s \in Server: state[s] = "Leader" /\ currentTerm[s] = t}) <= 1

\* A leader's log is never overwritten.
LeaderLogsAppendOnly ==
    \A s \in Server:
        (state[s] = "Leader") => (log'[s] = log[s] \/ Len(log'[s]) > Len(log[s]))

\* If two logs contain an entry with the same index and term, then the logs are
\* identical up to that index.
LogMatching ==
    \A s1, s2 \in Server:
        \A i \in 1..Min({Len(log[s1]), Len(log[s2])}):
            (log[s1][i].term = log[s2][i].term) => (log[s1][i] = log[s2][i])

\* If a server has applied an entry, no other server can apply a different one.
StateMachineSafety ==
    \A s1, s2 \in Server:
        \A i \in 1..Min({appliedIndex[s1], appliedIndex[s2]}):
            log[s1][i] = log[s2][i]

\* The commitIndex is monotonic for each server.
CommitIndexMonotonic ==
    \A s \in Server: commitIndex'[s] >= commitIndex[s]

\* The term is monotonic for each server.
TermMonotonic ==
    \A s \in Server: currentTerm'[s] >= currentTerm[s]

====