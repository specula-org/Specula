---- MODULE etcdraft ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    \* @type: Set(Str);
    Server,
    \* @type: Set(Str);
    Key,
    \* @type: Set(Int);
    Value,
    \* @type: Int;
    Nil,
    \* @type: Int;
    ElectionTimeoutMin,
    \* @type: Int;
    ElectionTimeoutMax,
    \* @type: Int;
    HeartbeatTimeout

ASSUME /\ ElectionTimeoutMin > HeartbeatTimeout
       /\ ElectionTimeoutMin =< ElectionTimeoutMax

\* A client command to be applied to the state machine.
ClientCommand == [ op: {"GET", "PUT", "DELETE"}, key: Key, value: Value ]

\* A log entry
LogEntry == [ term: Nat, command: ClientCommand ]

\* Message types
MsgType == {
    "AppendEntriesRequest", "AppendEntriesResponse",
    "RequestVoteRequest", "RequestVoteResponse",
    "PreVoteRequest", "PreVoteResponse",
    "ClientRequest", "ClientResponse",
    "Heartbeat", "HeartbeatResponse",
    "TimeoutNow"
}

\* Server states
ServerState == {"follower", "candidate", "precandidate", "leader"}

VARIABLES
    \* Per-server state
    \* @type: [Server -> Str];
    state,
    \* @type: [Server -> Nat];
    currentTerm,
    \* @type: [Server -> Server \cup {Nil}];
    votedFor,
    \* @type: [Server -> Seq(LogEntry)];
    log,
    \* @type: [Server -> Nat];
    commitIndex,
    \* @type: [Server -> Nat];
    appliedIndex,
    \* @type: [Server -> Server \cup {Nil}];
    lead,
    \* @type: [Server -> Server \cup {Nil}];
    leadTransferee,

    \* Leader-specific state
    \* @type: [Server -> [Server -> Nat]];
    nextIndex,
    \* @type: [Server -> [Server -> Nat]];
    matchIndex,

    \* Candidate-specific state
    \* @type: [Server -> Set(Server)];
    votesGranted,

    \* Timers
    \* @type: [Server -> Int];
    electionTimer,
    \* @type: [Server -> Int];
    heartbeatTimer,

    \* The network, represented as a bag of messages
    \* @type: Set(<<Str, Server, Server, Int, Seq(LogEntry), Int, Int, Int, BOOLEAN>>);
    messages,

    \* The key-value store for each server
    \* @type: [Server -> [Key -> Value]];
    kvStore

vars == <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
          nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer, messages, kvStore>>

\* Helper functions
Voters == Server
Quorum == (Cardinality(Voters) \div 2) + 1
LastLogIndex(s) == Len(log[s])
LastLogTerm(s) == IF LastLogIndex(s) = 0 THEN 0 ELSE log[s][LastLogIndex(s)].term

IsUpToDate(s, candLastLogIndex, candLastLogTerm) ==
    LET lastTerm == LastLogTerm(s)
        lastIndex == LastLogIndex(s)
    IN \/ candLastLogTerm > lastTerm
       \/ (candLastLogTerm = lastTerm /\ candLastLogIndex >= lastIndex)

\* Type invariant for all state variables
TypeOK ==
    /\ state \in [Server -> ServerState]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {Nil}]
    /\ \A s \in Server: log[s] \in Seq(LogEntry)
    /\ commitIndex \in [Server -> Nat]
    /\ appliedIndex \in [Server -> Nat]
    /\ lead \in [Server -> Server \cup {Nil}]
    /\ leadTransferee \in [Server -> Server \cup {Nil}]
    /\ nextIndex \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]
    /\ votesGranted \in [Server -> Set(Server)]
    /\ electionTimer \in [Server -> Int]
    /\ heartbeatTimer \in [Server -> Int]
    /\ \A s \in Server: appliedIndex[s] <= commitIndex[s]
    /\ \A s \in Server: commitIndex[s] <= Len(log[s])
    /\ kvStore \in [Server -> [Key -> Value]]

\* Initial state of the system
Init ==
    /\ state = [s \in Server |-> "follower"]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> Nil]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ appliedIndex = [s \in Server |-> 0]
    /\ lead = [s \in Server |-> Nil]
    /\ leadTransferee = [s \in Server |-> Nil]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ votesGranted = [s \in Server |-> {}]
    /\ electionTimer = [s \in Server |-> 0]
    /\ heartbeatTimer = [s \in Server |-> 0]
    /\ messages = {}
    /\ kvStore = [s \in Server |-> [k \in Key |-> Nil]]

\* Actions

\* A client submits a request to a server
ClientRequest(s, cmd) ==
    /\ state[s] = "leader"
    /\ \/ cmd.op = "PUT"
       \/ cmd.op = "DELETE"
    /\ LET newEntry == [term |-> currentTerm[s], command |-> cmd]
       IN log' = [log EXCEPT ![s] = log[s] \o <<newEntry>>]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex, lead, leadTransferee,
                   nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer, messages, kvStore>>

\* A server's election timer times out
Timeout(s) ==
    /\ state[s] \in {"follower", "candidate", "precandidate"}
    /\ electionTimer[s] >=
        CASE state[s] = "follower" -> ElectionTimeoutMin
             [] state[s] = "candidate" -> ElectionTimeoutMin
             [] state[s] = "precandidate" -> ElectionTimeoutMin
    /\ state' = [state EXCEPT ![s] = "precandidate"]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ messages' = messages \cup
        { [ type |-> "PreVoteRequest",
            from |-> s,
            to |-> p,
            term |-> currentTerm[s] + 1,
            lastLogIndex |-> LastLogIndex(s),
            lastLogTerm |-> LastLogTerm(s)
          ] : p \in Voters \ {s} }
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                   nextIndex, matchIndex, heartbeatTimer, kvStore>>

\* A precandidate gets enough pre-votes and becomes a candidate
BecomeCandidate(s) ==
    /\ state[s] = "precandidate"
    /\ Cardinality(votesGranted[s]) >= Quorum
    /\ state' = [state EXCEPT ![s] = "candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ messages' = messages \cup
        { [ type |-> "RequestVoteRequest",
            from |-> s,
            to |-> p,
            term |-> currentTerm'[s],
            lastLogIndex |-> LastLogIndex(s),
            lastLogTerm |-> LastLogTerm(s)
          ] : p \in Voters \ {s} }
    /\ UNCHANGED <<log, commitIndex, appliedIndex, lead, leadTransferee,
                   nextIndex, matchIndex, heartbeatTimer, kvStore>>

\* A candidate gets enough votes and becomes a leader
BecomeLeader(s) ==
    /\ state[s] = "candidate"
    /\ Cardinality(votesGranted[s]) >= Quorum
    /\ state' = [state EXCEPT ![s] = "leader"]
    /\ lead' = [lead EXCEPT ![s] = s]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Server |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Server |-> 0]]
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
    /\ log' = [log EXCEPT ![s] = log[s] \o <<[term |-> currentTerm[s], command |-> [op |-> "PUT", key |-> "noop", value |-> 0]]>>]
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, appliedIndex, leadTransferee,
                   votesGranted, electionTimer, messages, kvStore>>

\* A server steps down to follower state
BecomeFollower(s, newTerm) ==
    /\ currentTerm[s] < newTerm
    /\ state' = [state EXCEPT ![s] = "follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = newTerm]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ lead' = [lead EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, appliedIndex, leadTransferee, nextIndex, matchIndex,
                   votesGranted, electionTimer, heartbeatTimer, messages, kvStore>>

\* Leader sends AppendEntries or Heartbeat to a follower
SendAppendEntries(s, p) ==
    /\ state[s] = "leader"
    /\ p \in Voters \ {s}
    /\ LET prevLogIndex == nextIndex[s][p] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[s][prevLogIndex].term ELSE 0
           entriesToSend == SubSeq(log[s], nextIndex[s][p], LastLogIndex(s))
    IN /\ \/ entriesToSend /= <<>>  \* Send if there are entries
          \/ heartbeatTimer[s] >= HeartbeatTimeout \* Or if heartbeat timeout
       /\ messages' = messages \cup
            { [ type |-> "AppendEntriesRequest",
                from |-> s,
                to |-> p,
                term |-> currentTerm[s],
                prevLogIndex |-> prevLogIndex,
                prevLogTerm |-> prevLogTerm,
                entries |-> entriesToSend,
                leaderCommit |-> commitIndex[s]
              ] }
       /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                      nextIndex, matchIndex, votesGranted, electionTimer, kvStore>>

\* A server receives a message
Receive(m) ==
    LET s == m.to
    IN
    \/ /\ m.type = "PreVoteRequest"
       /\ LET candTerm == m.term
              candLastLogIndex == m.lastLogIndex
              candLastLogTerm == m.lastLogTerm
          IN /\ candTerm > currentTerm[s]
             /\ IsUpToDate(s, candLastLogIndex, candLastLogTerm)
             /\ messages' = messages \ {m} \cup
                  { [ type |-> "PreVoteResponse",
                      from |-> s,
                      to |-> m.from,
                      term |-> candTerm,
                      voteGranted |-> TRUE
                    ] }
             /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                            nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer, kvStore>>
    \/ /\ m.type = "RequestVoteRequest"
       /\ LET candTerm == m.term
              candidateId == m.from
              candLastLogIndex == m.lastLogIndex
              candLastLogTerm == m.lastLogTerm
              grantVote == /\ candTerm > currentTerm[s]
                           /\ IsUpToDate(s, candLastLogIndex, candLastLogTerm)
                           \/ /\ candTerm = currentTerm[s]
                              /\ votedFor[s] \in {Nil, candidateId}
                              /\ IsUpToDate(s, candLastLogIndex, candLastLogTerm)
       IN /\ messages' = messages \ {m} \cup
                { [ type |-> "RequestVoteResponse",
                    from |-> s,
                    to |-> candidateId,
                    term |-> IF grantVote THEN candTerm ELSE currentTerm[s],
                    voteGranted |-> grantVote
                  ] }
          /\ IF grantVote THEN
                /\ state' = [state EXCEPT ![s] = "follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![s] = candTerm]
                /\ votedFor' = [votedFor EXCEPT ![s] = candidateId]
                /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
                /\ UNCHANGED <<log, commitIndex, appliedIndex, lead, leadTransferee,
                               nextIndex, matchIndex, votesGranted, heartbeatTimer, kvStore>>
             ELSE
                UNCHANGED vars

    \/ /\ m.type \in {"PreVoteResponse", "RequestVoteResponse"}
       /\ state[s] \in {"candidate", "precandidate"}
       /\ m.term = IF m.type = "PreVoteResponse" THEN currentTerm[s] + 1 ELSE currentTerm[s]
       /\ messages' = messages \ {m}
       /\ IF m.voteGranted THEN
            votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {m.from}]
          ELSE
            UNCHANGED votesGranted
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                      nextIndex, matchIndex, electionTimer, heartbeatTimer, kvStore>>

    \/ /\ m.type = "AppendEntriesRequest"
       /\ LET leaderTerm == m.term
              prevLogIndex == m.prevLogIndex
              prevLogTerm == m.prevLogTerm
              entries == m.entries
              leaderCommit == m.leaderCommit
       IN /\ messages' = messages \ {m}
          /\ IF leaderTerm < currentTerm[s] THEN
                /\ messages' = messages \ {m} \cup
                    { [ type |-> "AppendEntriesResponse",
                        from |-> s,
                        to |-> m.from,
                        term |-> currentTerm[s],
                        success |-> FALSE,
                        matchIndex |-> 0
                      ] }
                /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                               nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer, kvStore>>
             ELSE
                /\ state' = [state EXCEPT ![s] = "follower"]
                /\ currentTerm' = [currentTerm EXCEPT ![s] = leaderTerm]
                /\ lead' = [lead EXCEPT ![s] = m.from]
                /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
                /\ LET logOk == /\ prevLogIndex <= LastLogIndex(s)
                                /\ (prevLogIndex = 0 \/ log[s][prevLogIndex].term = prevLogTerm)
                IN IF logOk THEN
                    /\ LET newLog == Head(log[s], prevLogIndex) \o entries
                    IN log' = [log EXCEPT ![s] = newLog]
                    /\ commitIndex' = [commitIndex EXCEPT ![s] = min(leaderCommit, LastLogIndex(s))]
                    /\ messages' = messages \ {m} \cup
                        { [ type |-> "AppendEntriesResponse",
                            from |-> s,
                            to |-> m.from,
                            term |-> currentTerm'[s],
                            success |-> TRUE,
                            matchIndex |-> LastLogIndex(s)
                          ] }
                    /\ UNCHANGED <<votedFor, appliedIndex, leadTransferee, nextIndex, matchIndex,
                                   votesGranted, heartbeatTimer, kvStore>>
                   ELSE
                    /\ messages' = messages \ {m} \cup
                        { [ type |-> "AppendEntriesResponse",
                            from |-> s,
                            to |-> m.from,
                            term |-> currentTerm'[s],
                            success |-> FALSE,
                            matchIndex |-> 0
                          ] }
                    /\ UNCHANGED <<log, commitIndex, votedFor, appliedIndex, leadTransferee, nextIndex,
                                   matchIndex, votesGranted, heartbeatTimer, kvStore>>

    \/ /\ m.type = "AppendEntriesResponse"
       /\ state[s] = "leader"
       /\ m.term = currentTerm[s]
       /\ messages' = messages \ {m}
       /\ IF m.success THEN
            /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.matchIndex + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = m.matchIndex]
            /\ LET newCommitIndex ==
                    LET M == { i \in 1..LastLogIndex(s) :
                                /\ i > commitIndex[s]
                                /\ log[s][i].term = currentTerm[s]
                                /\ Cardinality({p \in Voters : matchIndex[s][p] >= i}) >= Quorum }
                    IN IF M = {} THEN commitIndex[s] ELSE Max(M)
               IN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
            /\ UNCHANGED <<state, currentTerm, votedFor, log, appliedIndex, lead, leadTransferee,
                           votesGranted, electionTimer, heartbeatTimer, kvStore>>
          ELSE
            /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = max(1, nextIndex[s][m.from] - 1)]
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                           matchIndex, votesGranted, electionTimer, heartbeatTimer, kvStore>>

\* A server applies a committed entry to its state machine
Apply(s) ==
    /\ appliedIndex[s] < commitIndex[s]
    /\ LET idx == appliedIndex[s] + 1
           cmd == log[s][idx].command
    IN /\ appliedIndex' = [appliedIndex EXCEPT ![s] = idx]
       /\ IF cmd.op = "PUT" THEN
            kvStore' = [kvStore EXCEPT ![s][cmd.key] = cmd.value]
          ELSE IF cmd.op = "DELETE" THEN
            kvStore' = [kvStore EXCEPT ![s][cmd.key] = Nil]
          ELSE
            UNCHANGED kvStore
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, lead, leadTransferee,
                   nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer, messages>>

\* Advance timers
AdvanceTime ==
    /\ electionTimer' = [s \in Server |-> electionTimer[s] + 1]
    /\ heartbeatTimer' = [s \in Server |-> heartbeatTimer[s] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                   nextIndex, matchIndex, votesGranted, messages, kvStore>>

\* A message is lost
DropMessage(m) ==
    /\ m \in messages
    /\ messages' = messages \ {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                   nextIndex, matchIndex, votesGranted, electionTimer, heartbeatTimer, kvStore>>

\* A server crashes
Crash(s) ==
    /\ state' = [state EXCEPT ![s] = "follower"]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = -1] \* Special value to indicate crashed
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                   nextIndex, matchIndex, votesGranted, heartbeatTimer, messages, kvStore>>

\* A server recovers
Recover(s) ==
    /\ electionTimer[s] = -1
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, lead, leadTransferee,
                   nextIndex, matchIndex, votesGranted, heartbeatTimer, messages, kvStore>>

Next ==
    \/ \E s \in Server, cmd \in ClientCommand : ClientRequest(s, cmd)
    \/ \E s \in Server : Timeout(s)
    \/ \E s \in Server : BecomeCandidate(s)
    \/ \E s \in Server : BecomeLeader(s)
    \/ \E s \in Server, t \in Nat : BecomeFollower(s, t)
    \/ \E s, p \in Server : SendAppendEntries(s, p)
    \/ \E m \in messages : Receive(m)
    \/ \E s \in Server : Apply(s)
    \/ AdvanceTime
    \/ \E m \in messages : DropMessage(m)
    \/ \E s \in Server : Crash(s)
    \/ \E s \in Server : Recover(s)

Spec == Init /\ [][Next]_vars

\* Safety Properties
LeaderElectionSafety ==
    \A t \in DOMAIN currentTerm:
        Cardinality({s \in Server : state[s] = "leader" /\ currentTerm[s] = t}) <= 1

LogMatchingProperty ==
    \A s1, s2 \in Server:
        \A i \in 1..min(Len(log[s1]), Len(log[s2])):
            (log[s1][i].term = log[s2][i].term) => (log[s1][i] = log[s2][i])

LeaderCompleteness ==
    \A t \in Nat, i \in Nat:
        ( \E s \in Server: i <= commitIndex[s] /\ log[s][i].term = t ) =>
            ( \A l \in Server, t2 \in Nat:
                (state[l] = "leader" /\ currentTerm[l] = t2 /\ t2 > t) =>
                    (i <= Len(log[l]) /\ log[l][i].term = t) )

StateMachSafety ==
    \A s1, s2 \in Server:
        \A i \in 1..min(appliedIndex[s1], appliedIndex[s2]):
            log[s1][i] = log[s2][i]

AppliedAreCommitted ==
    \A s \in Server: appliedIndex[s] <= commitIndex[s]

CommittedLogsAreDurable ==
    \A s1, s2 \in Server:
        LET oldLog1 == log[s1]
            oldLog2 == log[s2]
        IN [][
            /\ log[s1] = oldLog1
            /\ log[s2] = oldLog2
           => \A i \in 1..min(commitIndex[s1], commitIndex[s2]):
                oldLog1[i] = oldLog2[i]
           ]_vars

\* Liveness Properties
EventualLeaderElection ==
    []<>( \E s \in Server: state[s] = "leader" )

CommittedEntriesEventuallyApplied ==
    \A s \in Server:
        (commitIndex[s] > appliedIndex[s]) ~> (appliedIndex'[s] > appliedIndex[s])

=============================================================================
