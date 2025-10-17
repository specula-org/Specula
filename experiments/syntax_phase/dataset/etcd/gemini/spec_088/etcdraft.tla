---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, Reals

CONSTANTS
    \* @type: Set(Str);
    Servers,
    \* @type: Set(Str);
    Clients,
    \* @type: Set(Str);
    Keys,
    \* @type: Set(Str);
    Values

ASSUME Servers \subseteq {"n1", "n2", "n3"}
ASSUME Clients \subseteq {"c1"}
ASSUME Keys \subseteq {"k1"}
ASSUME Values \subseteq {"v1", "v2"}

\* System configuration
CONSTANTS
    ElectionTimeout,
    HeartbeatTimeout

ASSUME ElectionTimeout \in {4, 5, 6}
ASSUME HeartbeatTimeout = 2

\* Raft server states
ServerStates == {"Follower", "PreCandidate", "Candidate", "Leader"}

\* Raft message types
MessageTypes ==
    { "ClientRequest", "ClientResponse",
      "RequestVoteRequest", "RequestVoteResponse",
      "PreVoteRequest", "PreVoteResponse",
      "AppendEntriesRequest", "AppendEntriesResponse",
      "TimeoutNow", "Hup" }

\* Log entry types
EntryTypes == {"Normal", "ConfChange"}

\* A special value representing no one
None == "None"
AllNodes == Servers \cup {None}

\* A client operation
ClientOp == [type: {"Put"}, key: Keys, value: Values]

\* A log entry
LogEntry == [term: Nat, index: Nat, data: ClientOp \cup {"NoOp"}, type: EntryTypes, client: Clients \cup {None}]

\* A message on the network
Message == [
    from: AllNodes,
    to: Servers,
    type: MessageTypes,
    term: Nat,
    \* For AppendEntriesRequest
    prevLogIndex: Nat,
    prevLogTerm: Nat,
    entries: Seq(LogEntry),
    leaderCommit: Nat,
    \* For RequestVoteRequest
    lastLogIndex: Nat,
    lastLogTerm: Nat,
    \* For responses
    voteGranted: BOOLEAN,
    success: BOOLEAN,
    matchIndex: Nat,
    \* For client messages
    reqId: Nat,
    op: ClientOp
]

\* The set of all possible logs
Logs == UNION { Seq(S) : S \in SUBSET LogEntry }

\* The set of all possible key-value stores
KVStores == [Keys -> Values \cup {"null"}]

\* The set of all possible client request records
ClientRequestRecords == [
    id: Nat,
    client: Clients,
    op: ClientOp,
    server: Servers,
    status: {"pending", "committed", "responded"}
]

-----------------------------------------------------------------------------
VARIABLES
    \* Per-server state
    currentTerm,
    votedFor,
    raftState,
    log,
    commitIndex,
    appliedIndex,
    kvStore,

    \* Leader-specific state
    nextIndex,
    matchIndex,

    \* Candidate-specific state
    votesGranted,

    \* Timers
    electionTimer,
    heartbeatTimer,

    \* The network
    messages,

    \* Client interaction state
    clientRequests,
    nextReqId,

    \* Liveness and safety properties
    history,
    leader

\* PlusCal variables
vars == << currentTerm, votedFor, raftState, log, commitIndex, appliedIndex, kvStore,
           nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer,
           messages, clientRequests, nextReqId, history, leader >>

-----------------------------------------------------------------------------
TypeOK ==
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> AllNodes]
    /\ raftState \in [Servers -> ServerStates]
    /\ \A s \in Servers: log[s] \in Logs
    /\ commitIndex \in [Servers -> Nat]
    /\ appliedIndex \in [Servers -> Nat]
    /\ kvStore \in [Servers -> KVStores]
    /\ nextIndex \in [Servers -> [Servers -> Nat]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ votesGranted \in [Servers -> SUBSET Servers]
    /\ electionTimer \in [Servers -> 0..ElectionTimeout]
    /\ heartbeatTimer \in [Servers -> 0..HeartbeatTimeout]
    /\ messages \in SUBSET Message
    /\ clientRequests \in SUBSET ClientRequestRecords
    /\ nextReqId \in Nat
    /\ history \in Seq([type: {"invoke", "ok"}, client: Clients, op: ClientOp, value: Values \cup {"null"}])
    /\ leader \in [Nat -> SUBSET Servers]

-----------------------------------------------------------------------------
\* Helper functions and operators

QuorumSize == (Cardinality(Servers) \div 2) + 1

LastLogIndex(s) == Len(log[s])
LastLogTerm(s) == IF LastLogIndex(s) = 0 THEN 0 ELSE log[s][LastLogIndex(s)].term

IsUpToDate(s, m) ==
    LET myLastTerm == LastLogTerm(s) IN
    LET myLastIndex == LastLogIndex(s) IN
    \/ m.lastLogTerm > myLastTerm
    \/ (m.lastLogTerm = myLastTerm /\ m.lastLogIndex >= myLastIndex)

\* Send a message by adding it to the network message set
Send(m) == messages' = messages \cup {m}

\* Reset a server's state when it becomes a follower
ResetFollowerState(s, term) ==
    /\ raftState' = [raftState EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = None]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = ElectionTimeout]
    /\ UNCHANGED << kvStore, log, commitIndex, appliedIndex, nextIndex, matchIndex,
                    votesGranted, heartbeatTimer, messages, clientRequests, nextReqId, history, leader >>

-----------------------------------------------------------------------------
Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> None]
    /\ raftState = [s \in Servers |-> "Follower"]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ appliedIndex = [s \in Servers |-> 0]
    /\ kvStore = [s \in Servers |-> [k \in Keys |-> "null"]]
    /\ nextIndex = [s \in Servers |-> [p \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [p \in Servers |-> 0]]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ electionTimer = [s \in Servers |-> ElectionTimeout]
    /\ heartbeatTimer = [s \in Servers |-> HeartbeatTimeout]
    /\ messages = {}
    /\ clientRequests = {}
    /\ nextReqId = 1
    /\ history = << >>
    /\ leader = [t \in 0..0 |-> {}]

-----------------------------------------------------------------------------
\* Actions that model the Raft algorithm

\* A server's election timer times out, causing it to start a (pre)-election.
Timeout(s) ==
    /\ raftState[s] \in {"Follower", "Candidate", "PreCandidate"}
    /\ electionTimer[s] = 0
    /\ LET newTerm == currentTerm[s] + 1 IN
        /\ raftState' = [raftState EXCEPT ![s] = "PreCandidate"]
        /\ electionTimer' = [electionTimer EXCEPT ![s] = ElectionTimeout]
        /\ messages' = messages \cup
            {[ from |-> s, to |-> p, type |-> "PreVoteRequest", term |-> newTerm,
               lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s),
               prevLogIndex |-> 0, entries |-> << >>, leaderCommit |-> 0,
               voteGranted |-> FALSE, success |-> FALSE, matchIndex |-> 0,
               reqId |-> 0, op |-> [type |-> "Put", key |-> "k1", value |-> "v1"]
             ] : p \in Servers \ {s}}
    /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, appliedIndex, kvStore,
                    nextIndex, matchIndex, votesGranted, heartbeatTimer,
                    clientRequests, nextReqId, history, leader >>

\* A leader's heartbeat timer times out, causing it to send heartbeats.
Heartbeat(s) ==
    /\ raftState[s] = "Leader"
    /\ heartbeatTimer[s] = 0
    /\ messages' = messages \cup
        {[ from |-> s, to |-> p, type |-> "AppendEntriesRequest", term |-> currentTerm[s],
           prevLogIndex |-> LastLogIndex(log[s]), prevLogTerm |-> LastLogTerm(s),
           entries |-> << >>, leaderCommit |-> commitIndex[s],
           lastLogIndex |-> 0, lastLogTerm |-> 0,
           voteGranted |-> FALSE, success |-> FALSE, matchIndex |-> 0,
           reqId |-> 0, op |-> [type |-> "Put", key |-> "k1", value |-> "v1"]
         ] : p \in Servers \ {s}}
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = HeartbeatTimeout]
    /\ UNCHANGED << currentTerm, votedFor, raftState, log, commitIndex, appliedIndex, kvStore,
                    nextIndex, matchIndex, votesGranted, electionTimer,
                    clientRequests, nextReqId, history, leader >>

\* A server receives a message from the network.
Receive(m) ==
    /\ m \in messages
    /\ LET s == m.to IN
       /\ IF m.term > currentTerm[s]
          THEN /\ \/ m.type \in {"AppendEntriesRequest", "RequestVoteRequest"}
                  \/ (m.type = "PreVoteRequest" /\ m.term > currentTerm[s] + 1)
               /\ ResetFollowerState(s, m.term)
          ELSE /\ TRUE
               /\ UNCHANGED <<currentTerm, votedFor, raftState, electionTimer>>
    /\ \/ HandleAppendEntriesRequest(m)
       \/ HandleAppendEntriesResponse(m)
       \/ HandleVoteRequest(m)
       \/ HandleVoteResponse(m)
       \/ HandleClientRequest(m)
    /\ messages' = messages \ {m}

\* Handler for AppendEntriesRequest (includes heartbeats)
HandleAppendEntriesRequest(m) ==
    /\ m.type = "AppendEntriesRequest"
    /\ LET s == m.to IN
    /\ LET newVars == << currentTerm, votedFor, raftState, log, commitIndex, appliedIndex, kvStore,
                         nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer,
                         clientRequests, nextReqId, history, leader >> IN
    /\ IF m.term < currentTerm[s]
       THEN /\ Send([ from |-> s, to |-> m.from, type |-> "AppendEntriesResponse",
                      term |-> currentTerm[s], success |-> FALSE, matchIndex |-> 0,
                      prevLogIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0,
                      entries |-> << >>, leaderCommit |-> 0, voteGranted |-> FALSE,
                      reqId |-> 0, op |-> [type |-> "Put", key |-> "k1", value |-> "v1"]
                    ])
            /\ UNCHANGED newVars
       ELSE /\ electionTimer' = [electionTimer EXCEPT ![s] = ElectionTimeout]
            /\ raftState' = [raftState EXCEPT ![s] = "Follower"]
            /\ LET logOK == \/ m.prevLogIndex = 0
                           \/ (/\ m.prevLogIndex <= Len(log[s])
                               /\ log[s][m.prevLogIndex].term = m.prevLogTerm) IN
               IF logOK
               THEN /\ LET newEntries == m.entries IN
                    /\ LET conflictIndex ==
                           CHOOSE i \in 1..Len(newEntries):
                               /\ m.prevLogIndex + i <= Len(log[s])
                               /\ log[s][m.prevLogIndex + i].term /= newEntries[i].term
                    /\ log' = [log EXCEPT ![s] =
                        IF conflictIndex = UNDEFINED
                        THEN log[s] \o newEntries
                        ELSE SubSeq(log[s], 1, m.prevLogIndex + conflictIndex - 1) \o newEntries]
                    /\ IF m.leaderCommit > commitIndex[s]
                       THEN commitIndex' = [commitIndex EXCEPT ![s] = Min({m.leaderCommit, LastLogIndex(s)})]
                       ELSE UNCHANGED commitIndex
                    /\ Send([ from |-> s, to |-> m.from, type |-> "AppendEntriesResponse",
                              term |-> currentTerm[s], success |-> TRUE,
                              matchIndex |-> m.prevLogIndex + Len(m.entries),
                              prevLogIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0,
                              entries |-> << >>, leaderCommit |-> 0, voteGranted |-> FALSE,
                              reqId |-> 0, op |-> [type |-> "Put", key |-> "k1", value |-> "v1"]
                            ])
               ELSE /\ Send([ from |-> s, to |-> m.from, type |-> "AppendEntriesResponse",
                              term |-> currentTerm[s], success |-> FALSE, matchIndex |-> 0,
                              prevLogIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0,
                              entries |-> << >>, leaderCommit |-> 0, voteGranted |-> FALSE,
                              reqId |-> 0, op |-> [type |-> "Put", key |-> "k1", value |-> "v1"]
                            ])
                    /\ UNCHANGED <<log, commitIndex>>
            /\ UNCHANGED << currentTerm, votedFor, appliedIndex, kvStore, nextIndex, matchIndex,
                            votesGranted, heartbeatTimer, clientRequests, nextReqId, history, leader >>

\* Handler for AppendEntriesResponse
HandleAppendEntriesResponse(m) ==
    /\ m.type = "AppendEntriesResponse"
    /\ LET s == m.to IN
    /\ LET follower == m.from IN
    /\ LET newVars == << currentTerm, votedFor, raftState, log, commitIndex, appliedIndex, kvStore,
                         nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer,
                         clientRequests, nextReqId, history, leader >> IN
    /\ IF raftState[s] = "Leader" /\ m.term = currentTerm[s]
       THEN /\ IF m.success
               THEN /\ nextIndex' = [nextIndex EXCEPT ![s][follower] = m.matchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![s][follower] = m.matchIndex]
                    /\ LET newCommitIndex ==
                           CHOOSE N \in (commitIndex[s]+1)..LastLogIndex(s):
                               /\ log[s][N].term = currentTerm[s]
                               /\ Cardinality({p \in Servers: matchIndex[s][p] >= N}) >= QuorumSize
                    /\ IF newCommitIndex /= UNDEFINED
                       THEN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                       ELSE UNCHANGED commitIndex
               ELSE /\ nextIndex' = [nextIndex EXCEPT ![s][follower] = Max({1, nextIndex[s][follower] - 1})]
                    /\ UNCHANGED <<matchIndex, commitIndex>>
            /\ UNCHANGED << currentTerm, votedFor, raftState, log, appliedIndex, kvStore,
                            votesGranted, electionTimer, heartbeatTimer, clientRequests,
                            nextReqId, history, leader >>
       ELSE /\ UNCHANGED newVars

\* Handler for RequestVoteRequest and PreVoteRequest
HandleVoteRequest(m) ==
    /\ m.type \in {"RequestVoteRequest", "PreVoteRequest"}
    /\ LET s == m.to IN
    /\ LET grantVote ==
        /\ IsUpToDate(s, m)
        /\ IF m.type = "RequestVoteRequest"
           THEN m.term = currentTerm[s] /\ (votedFor[s] = None \/ votedFor[s] = m.from)
           ELSE TRUE
    /\ LET respType == IF m.type = "RequestVoteRequest" THEN "RequestVoteResponse" ELSE "PreVoteResponse" IN
    /\ Send([ from |-> s, to |-> m.from, type |-> respType,
              term |-> currentTerm[s], voteGranted |-> grantVote,
              success |-> FALSE, matchIndex |-> 0, prevLogIndex |-> 0, lastLogIndex |-> 0,
              lastLogTerm |-> 0, entries |-> << >>, leaderCommit |-> 0,
              reqId |-> 0, op |-> [type |-> "Put", key |-> "k1", value |-> "v1"]
            ])
    /\ IF grantVote /\ m.type = "RequestVoteRequest"
       THEN /\ votedFor' = [votedFor EXCEPT ![s] = m.from]
            /\ electionTimer' = [electionTimer EXCEPT ![s] = ElectionTimeout]
       ELSE UNCHANGED <<votedFor, electionTimer>>
    /\ UNCHANGED << currentTerm, raftState, log, commitIndex, appliedIndex, kvStore,
                    nextIndex, matchIndex, votesGranted, heartbeatTimer,
                    clientRequests, nextReqId, history, leader >>

\* Handler for RequestVoteResponse and PreVoteResponse
HandleVoteResponse(m) ==
    /\ m.type \in {"RequestVoteResponse", "PreVoteResponse"}
    /\ LET s == m.to IN
    /\ LET newVars == << currentTerm, votedFor, raftState, log, commitIndex, appliedIndex, kvStore,
                         nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer,
                         clientRequests, nextReqId, history, leader >> IN
    /\ LET isPreVoteResp == m.type = "PreVoteResponse" IN
    /\ LET isCorrectState == IF isPreVoteResp THEN raftState[s] = "PreCandidate" ELSE raftState[s] = "Candidate" IN
    /\ IF isCorrectState /\ m.term = currentTerm[s] /\ m.voteGranted
       THEN /\ LET newVotes == votesGranted[s] \cup {m.from} IN
            /\ IF Cardinality(newVotes) + 1 >= QuorumSize
               THEN /\ IF isPreVoteResp
                       THEN (* Start real election *)
                            /\ raftState' = [raftState EXCEPT ![s] = "Candidate"]
                            /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                            /\ votedFor' = [votedFor EXCEPT ![s] = s]
                            /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
                            /\ messages' = messages \cup
                                {[ from |-> s, to |-> p, type |-> "RequestVoteRequest", term |-> currentTerm[s] + 1,
                                   lastLogIndex |-> LastLogIndex(s), lastLogTerm |-> LastLogTerm(s),
                                   prevLogIndex |-> 0, entries |-> << >>, leaderCommit |-> 0,
                                   voteGranted |-> FALSE, success |-> FALSE, matchIndex |-> 0,
                                   reqId |-> 0, op |-> [type |-> "Put", key |-> "k1", value |-> "v1"]
                                 ] : p \in Servers \ {s}}
                            /\ UNCHANGED <<log, commitIndex, appliedIndex, kvStore, nextIndex, matchIndex,
                                            electionTimer, heartbeatTimer, clientRequests, nextReqId, history, leader>>
                       ELSE (* Become leader *)
                            /\ raftState' = [raftState EXCEPT ![s] = "Leader"]
                            /\ leader' = [leader EXCEPT ![currentTerm[s]] = {s}]
                            /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(s) + 1]]
                            /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0]]
                            /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
                            /\ log' = [log EXCEPT ![s] = log[s] \o <<[term |-> currentTerm[s], index |-> LastLogIndex(s) + 1, data |-> "NoOp", type |-> "Normal", client |-> None]>>]
                            /\ UNCHANGED <<currentTerm, votedFor, votesGranted, electionTimer, messages,
                                            commitIndex, appliedIndex, kvStore, clientRequests, nextReqId, history>>
               ELSE /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                    /\ UNCHANGED << currentTerm, votedFor, raftState, log, commitIndex, appliedIndex, kvStore,
                                    nextIndex, matchIndex, electionTimer, heartbeatTimer, messages,
                                    clientRequests, nextReqId, history, leader >>
       ELSE /\ UNCHANGED newVars

\* Handler for client requests
HandleClientRequest(m) ==
    /\ m.type = "ClientRequest"
    /\ LET s == m.to IN
    /\ IF raftState[s] = "Leader"
       THEN /\ LET newEntry == [term |-> currentTerm[s], index |-> LastLogIndex(s) + 1,
                                data |-> m.op, type |-> "Normal", client |-> m.from] IN
            /\ log' = [log EXCEPT ![s] = log[s] \o <<newEntry>>]
            /\ clientRequests' = clientRequests \cup {[id |-> m.reqId, client |-> m.from, op |-> m.op, server |-> s, status |-> "pending"]}
            /\ history' = Append(history, [type |-> "invoke", client |-> m.from, op |-> m.op, value |-> "null"])
            /\ UNCHANGED << currentTerm, votedFor, raftState, commitIndex, appliedIndex, kvStore,
                            nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer, messages, nextReqId, leader >>
       ELSE /\ LET l == CHOOSE l \in Servers: raftState[l] = "Leader" IN
            /\ IF l /= UNDEFINED
               THEN Send([from |-> m.from, to |-> l, type |-> "ClientRequest", term |-> 0, reqId |-> m.reqId, op |-> m.op,
                           prevLogIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0, entries |-> << >>,
                           leaderCommit |-> 0, voteGranted |-> FALSE, success |-> FALSE, matchIndex |-> 0])
               ELSE UNCHANGED messages
            /\ UNCHANGED << vars >>

\* A server applies a committed log entry to its state machine.
Apply(s) ==
    /\ appliedIndex[s] < commitIndex[s]
    /\ LET i == appliedIndex[s] + 1 IN
    /\ LET entry == log[s][i] IN
    /\ appliedIndex' = [appliedIndex EXCEPT ![s] = i]
    /\ IF entry.data /= "NoOp"
       THEN /\ kvStore' = [kvStore EXCEPT ![s][entry.data.key] = entry.data.value]
            /\ LET req == CHOOSE r \in clientRequests:
                            r.status = "pending" /\ r.op = entry.data
            /\ IF req /= UNDEFINED
               THEN /\ clientRequests' = (clientRequests \ {req}) \cup {[req EXCEPT !.status = "committed"]}
                    /\ Send([ from |-> s, to |-> req.client, type |-> "ClientResponse",
                              term |-> 0, success |-> TRUE, reqId |-> req.id,
                              op |-> [type |-> "Put", key |-> "k1", value |-> "v1"],
                              prevLogIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0,
                              entries |-> << >>, leaderCommit |-> 0, voteGranted |-> FALSE,
                              matchIndex |-> 0
                            ])
                    /\ history' = Append(history, [type |-> "ok", client |-> req.client, op |-> req.op, value |-> entry.data.value])
               ELSE UNCHANGED <<clientRequests, messages, history>>
       ELSE UNCHANGED <<kvStore, clientRequests, messages, history>>
    /\ UNCHANGED << currentTerm, votedFor, raftState, log, commitIndex,
                    nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer, nextReqId, leader >>

\* A client submits a new request to a random server.
ClientSubmit(c, s, op) ==
    /\ c \in Clients
    /\ s \in Servers
    /\ op \in ClientOp
    /\ Send([ from |-> c, to |-> s, type |-> "ClientRequest", term |-> 0,
              reqId |-> nextReqId, op |-> op,
              prevLogIndex |-> 0, lastLogIndex |-> 0, lastLogTerm |-> 0,
              entries |-> << >>, leaderCommit |-> 0, voteGranted |-> FALSE,
              success |-> FALSE, matchIndex |-> 0
            ])
    /\ nextReqId' = nextReqId + 1
    /\ UNCHANGED << vars >>

\* A client receives a response.
ClientReceiveResponse(m) ==
    /\ m.type = "ClientResponse"
    /\ m \in messages
    /\ LET req == CHOOSE r \in clientRequests: r.id = m.reqId /\ r.status = "committed"
    /\ req /= UNDEFINED
    /\ clientRequests' = (clientRequests \ {req}) \cup {[req EXCEPT !.status = "responded"]}
    /\ messages' = messages \ {m}
    /\ UNCHANGED << currentTerm, votedFor, raftState, log, commitIndex, appliedIndex, kvStore,
                    nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer, nextReqId, history, leader >>

\* Advance time by one tick.
Tick ==
    /\ electionTimer' = [s \in Servers |-> IF electionTimer[s] > 0 THEN electionTimer[s] - 1 ELSE 0]
    /\ heartbeatTimer' = [s \in Servers |-> IF heartbeatTimer[s] > 0 THEN heartbeatTimer[s] - 1 ELSE 0]
    /\ UNCHANGED << currentTerm, votedFor, raftState, log, commitIndex, appliedIndex, kvStore,
                    nextIndex, matchIndex, votesGranted, messages, clientRequests, nextReqId, history, leader >>

-----------------------------------------------------------------------------
Next ==
    \/ \E s \in Servers: Timeout(s)
    \/ \E s \in Servers: Heartbeat(s)
    \/ \E m \in messages: Receive(m)
    \/ \E s \in Servers: Apply(s)
    \/ \E c \in Clients, s \in Servers, op \in ClientOp: ClientSubmit(c, s, op)
    \/ \E m \in messages: ClientReceiveResponse(m)
    \/ Tick

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety Properties (Invariants)

\* At most one leader can exist in any given term.
ElectionSafety ==
    \A t \in DOMAIN leader: Cardinality(leader[t]) <= 1

\* A leader's log is never overwritten.
LeaderLogsOnlyAppend ==
    \A s \in Servers:
        /\ raftState[s] = "Leader" => log'[s] = log[s] \o <<...>>
        /\ raftState'[s] = "Leader" => log'[s] = log[s] \o <<...>>

\* If two logs contain an entry with the same index and term,
\* then the logs are identical up to that index.
LogMatching ==
    \A s1, s2 \in Servers, i \in 1..Min({Len(log[s1]), Len(log[s2])}):
        (log[s1][i].term = log[s2][i].term) => (log[s1][i] = log[s2][i])

\* If an entry is committed, it must be present in the logs of all future leaders.
LeaderCompleteness ==
    \A t1, t2 \in DOMAIN leader:
        /\ t2 > t1
        /\ leader[t1] /= {}
        /\ leader[t2] /= {}
        => LET l1 == CHOOSE s \in leader[t1]: TRUE IN
           LET l2 == CHOOSE s \in leader[t2]: TRUE IN
           \A i \in 1..commitIndex[l1]:
               \E j \in 1..Len(log[l2]): log[l2][j] = log[l1][i]

\* All state machines apply the same sequence of entries.
StateSafety ==
    \A s1, s2 \in Servers, i \in 1..Min({appliedIndex[s1], appliedIndex[s2]}):
        log[s1][i] = log[s2][i]

\* Terms only increase.
TermMonotonicity ==
    \A s \in Servers: currentTerm'[s] >= currentTerm[s]

\* Once a server votes for a candidate, it cannot vote for another in the same term.
VoteOncePerTerm ==
    \A s \in Servers:
        /\ votedFor[s] /= None => votedFor'[s] = votedFor[s] \/ currentTerm'[s] > currentTerm[s]

\* Committed entries are durable.
CommittedLogsDurable ==
    \A s \in Servers, i \in 1..commitIndex[s]:
        log'[s][i] = log[s][i]

-----------------------------------------------------------------------------
\* Liveness Properties

\* Eventually, a leader is elected.
EventuallyLeaderElected == <>(\E s \in Servers: raftState[s] = "Leader")

\* A submitted client request is eventually committed.
RequestEventuallyCommitted(reqId) ==
    (\E r \in clientRequests: r.id = reqId) ~> (\E r \in clientRequests: r.id = reqId /\ r.status /= "pending")

\* A committed client request is eventually responded to.
ResponseEventuallySent(reqId) ==
    (\E r \in clientRequests: r.id = reqId /\ r.status = "committed") ~> (\E r \in clientRequests: r.id = reqId /\ r.status = "responded")

=============================================================================
