---- MODULE etcdraft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    \* @type: Set(Str);
    Server,
    \* @type: Set(Str);
    Value,
    \* @type: Int;
    DefaultVote,
    \* @type: Int;
    HeartbeatTick,
    \* @type: Int;
    ElectionTick,
    \* @type: Bool;
    PreVoteEnabled,
    \* @type: Bool;
    CheckQuorumEnabled

ASSUME Server \subseteq {"n1", "n2", "n3"}
ASSUME Value \subseteq {"v1", "v2"}
ASSUME DefaultVote = 0
ASSUME HeartbeatTick = 1
ASSUME ElectionTick = 10
ASSUME PreVoteEnabled \in {TRUE, FALSE}
ASSUME CheckQuorumEnabled \in {TRUE, FALSE}

\* Message types from raftpb.proto
MsgHup             = "MsgHup"
MsgBeat            = "MsgBeat"
MsgProp            = "MsgProp"
MsgApp             = "MsgApp"
MsgAppResp         = "MsgAppResp"
MsgVote            = "MsgVote"
MsgVoteResp        = "MsgVoteResp"
MsgSnap            = "MsgSnap"
MsgHeartbeat       = "MsgHeartbeat"
MsgHeartbeatResp   = "MsgHeartbeatResp"
MsgUnreachable     = "MsgUnreachable"
MsgSnapStatus      = "MsgSnapStatus"
MsgCheckQuorum     = "MsgCheckQuorum"
MsgTransferLeader  = "MsgTransferLeader"
MsgTimeoutNow      = "MsgTimeoutNow"
MsgReadIndex       = "MsgReadIndex"
MsgReadIndexResp   = "MsgReadIndexResp"
MsgPreVote         = "MsgPreVote"
MsgPreVoteResp     = "MsgPreVoteResp"

MessageTypes = {MsgHup, MsgBeat, MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgSnap, MsgHeartbeat, MsgHeartbeatResp, MsgUnreachable, MsgSnapStatus, MsgCheckQuorum, MsgTransferLeader, MsgTimeoutNow, MsgReadIndex, MsgReadIndexResp, MsgPreVote, MsgPreVoteResp}

\* Raft node states
StateFollower     = "StateFollower"
StateCandidate    = "StateCandidate"
StateLeader       = "StateLeader"
StatePreCandidate = "StatePreCandidate"

RaftStates = {StateFollower, StateCandidate, StateLeader, StatePreCandidate}

VARIABLES
    \* Per-server state
    \* @type: [Server -> Str];
    state,
    \* @type: [Server -> Int];
    currentTerm,
    \* @type: [Server -> Int];
    votedFor,
    \* @type: [Server -> Seq([term: Int, value: Str, index: Int, type: Str])];
    log,
    \* @type: [Server -> Int];
    commitIndex,
    \* @type: [Server -> Int];
    appliedIndex,
    \* @type: [Server -> [Server -> Int]];
    nextIndex,
    \* @type: [Server -> [Server -> Int]];
    matchIndex,
    \* @type: [Server -> Int];
    leader,
    \* @type: [Server -> Set(Int)];
    votesGranted,
    \* @type: [Server -> Int];
    electionElapsed,
    \* @type: [Server -> Int];
    heartbeatElapsed,
    \* @type: [Server -> Int];
    randomizedElectionTimeout,
    \* @type: [Server -> Int];
    leadTransferee,
    \* @type: [Server -> Bool];
    recentActive,
    \* @type: Set([type: Str, to: Int, from: Int, term: Int, logTerm: Int, index: Int, entries: Seq, commit: Int, reject: Bool, rejectHint: Int]);
    network

vars == <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader, votesGranted, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive, network>>

Quorum == (Cardinality(Server) \div 2) + 1

\* Helper functions for log access
LastLogIndex(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].index
LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term
TermAt(l, i) == IF i > 0 /\ i <= Len(l) THEN l[i].term ELSE 0
IsUpToDate(l, candIndex, candTerm) ==
    LET lastTerm == LastLogTerm(l)
        lastIndex == LastLogIndex(l)
    IN (candTerm > lastTerm) \/ (candTerm = lastTerm /\ candIndex >= lastIndex)

\* State transition helpers
BecomeFollower(s, i, term, l) ==
    /\ state' = [state EXCEPT ![i] = StateFollower]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ votedFor' = [votedFor EXCEPT ![i] = DefaultVote]
    /\ leader' = [leader EXCEPT ![i] = l]
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ leadTransferee' = [leadTransferee EXCEPT ![i] = DefaultVote]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex, heartbeatElapsed, randomizedElectionTimeout, recentActive, network>>

BecomeCandidate(s, i) ==
    /\ state' = [state EXCEPT ![i] = StateCandidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ leader' = [leader EXCEPT ![i] = DefaultVote]
    /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive, network>>

BecomePreCandidate(s, i) ==
    /\ state' = [state EXCEPT ![i] = StatePreCandidate]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ leader' = [leader EXCEPT ![i] = DefaultVote]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex, nextIndex, matchIndex, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive, network>>

BecomeLeader(s, i) ==
    /\ state' = [state EXCEPT ![i] = StateLeader]
    /\ leader' = [leader EXCEPT ![i] = i]
    /\ leadTransferee' = [leadTransferee EXCEPT ![i] = DefaultVote]
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> LastLogIndex(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> IF j=i THEN LastLogIndex(log[i]) ELSE 0]]
    /\ recentActive' = [recentActive EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex, votesGranted, randomizedElectionTimeout, network>>

Init ==
    /\ state = [i \in Server |-> StateFollower]
    /\ currentTerm = [i \in Server |-> 0]
    /\ votedFor = [i \in Server |-> DefaultVote]
    /\ log = [i \in Server |-> <<>>]
    /\ commitIndex = [i \in Server |-> 0]
    /\ appliedIndex = [i \in Server |-> 0]
    /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
    /\ leader = [i \in Server |-> DefaultVote]
    /\ votesGranted = [i \in Server |-> {}]
    /\ electionElapsed = [i \in Server |-> 0]
    /\ heartbeatElapsed = [i \in Server |-> 0]
    /\ randomizedElectionTimeout = [i \in Server |-> ElectionTick] \* Simplified, could be randomized
    /\ leadTransferee = [i \in Server |-> DefaultVote]
    /\ recentActive = [i \in Server |-> TRUE]
    /\ network = {}

\* Client proposes a new value to be added to the log.
ClientRequest(i, val) ==
    /\ state[i] = StateLeader
    /\ leadTransferee[i] = DefaultVote
    /\ LET
        newEntry == [
            term |-> currentTerm[i],
            value |-> val,
            index |-> LastLogIndex(log[i]) + 1,
            type |-> "Normal"
        ]
        newLog == Append(log[i], newEntry)
       IN log' = [log EXCEPT ![i] = newLog]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![i] = LastLogIndex(log'[i])]]
    /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex, nextIndex, leader, votesGranted, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive, network>>

\* A server's timer ticks.
Tick(i) ==
    /\ state[i] \in {StateFollower, StateCandidate, StatePreCandidate}
        /\ electionElapsed' = [electionElapsed EXCEPT ![i] = electionElapsed[i] + 1]
        /\ UNCHANGED <<heartbeatElapsed>>
    /\ state[i] = StateLeader
        /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = heartbeatElapsed[i] + 1]
        /\ electionElapsed' = [electionElapsed EXCEPT ![i] = electionElapsed[i] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader, votesGranted, randomizedElectionTimeout, leadTransferee, recentActive, network>>

\* A follower or candidate times out and starts an election.
Timeout(i) ==
    /\ state[i] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ electionElapsed[i] >= randomizedElectionTimeout[i]
    /\ IF PreVoteEnabled
       THEN /\ BecomePreCandidate(i, i)
            /\ LET term == currentTerm[i] + 1
                   lastIdx == LastLogIndex(log[i])
                   lastTerm == LastLogTerm(log[i])
                   req(j) == [type |-> MsgPreVote, to |-> j, from |-> i, term |-> term,
                              logTerm |-> lastTerm, index |-> lastIdx, entries |-> <<>>,
                              commit |-> 0, reject |-> FALSE, rejectHint |-> 0]
               IN network' = network \cup {req(j) : j \in Server \ {i}}
       ELSE /\ BecomeCandidate(i, i)
            /\ LET term == currentTerm'[i]
                   lastIdx == LastLogIndex(log[i])
                   lastTerm == LastLogTerm(log[i])
                   req(j) == [type |-> MsgVote, to |-> j, from |-> i, term |-> term,
                              logTerm |-> lastTerm, index |-> lastIdx, entries |-> <<>>,
                              commit |-> 0, reject |-> FALSE, rejectHint |-> 0]
               IN network' = network \cup {req(j) : j \in Server \ {i}}
    /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive>>

\* A leader's heartbeat timer fires, so it sends heartbeats.
HeartbeatTimeout(i) ==
    /\ state[i] = StateLeader
    /\ heartbeatElapsed[i] >= HeartbeatTick
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![i] = 0]
    /\ LET req(j) == [type |-> MsgHeartbeat, to |-> j, from |-> i, term |-> currentTerm[i],
                      logTerm |-> 0, index |-> 0, entries |-> <<>>,
                      commit |-> Min({commitIndex[i], matchIndex[i][j]}),
                      reject |-> FALSE, rejectHint |-> 0]
       IN network' = network \cup {req(j) : j \in Server \ {i}}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader, votesGranted, electionElapsed, randomizedElectionTimeout, leadTransferee, recentActive>>

\* A leader checks if the quorum is still active.
CheckQuorum(i) ==
    /\ state[i] = StateLeader
    /\ CheckQuorumEnabled
    /\ electionElapsed[i] >= ElectionTick
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ LET activeNodes == {j \in Server : recentActive[j]} \cup {i}
       IN IF Cardinality(activeNodes) < Quorum
          THEN BecomeFollower(i, i, currentTerm[i], DefaultVote)
          ELSE /\ recentActive' = [j \in Server |-> FALSE]
               /\ UNCHANGED <<state, currentTerm, votedFor, leader, leadTransferee, votesGranted, log, commitIndex, appliedIndex, nextIndex, matchIndex, heartbeatElapsed, randomizedElectionTimeout, network>>

\* A leader sends AppendEntries RPCs to its followers.
SendAppendEntries(i, j) ==
    /\ state[i] = StateLeader
    /\ j \in Server \ {i}
    /\ LastLogIndex(log[i]) >= nextIndex[i][j]
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == TermAt(log[i], prevLogIndex)
           entriesToSend == SubSeq(log[i], nextIndex[i][j], LastLogIndex(log[i]))
           req == [type |-> MsgApp, to |-> j, from |-> i, term |-> currentTerm[i],
                   logTerm |-> prevLogTerm, index |-> prevLogIndex,
                   entries |-> entriesToSend, commit |-> commitIndex[i],
                   reject |-> FALSE, rejectHint |-> 0]
       IN network' = network \cup {req}
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![j] = LastLogIndex(log[i]) + 1]]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, matchIndex, leader, votesGranted, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive>>

\* A server receives a message from the network.
Receive(msg) ==
    /\ msg \in network
    /\ LET i == msg.to
    IN
    \/ /\ msg.term > currentTerm[i]
       /\ BecomeFollower(i, i, msg.term, IF msg.type \in {MsgApp, MsgHeartbeat} THEN msg.from ELSE DefaultVote)
       /\ network' = network \ {msg}
    \/ /\ msg.term < currentTerm[i]
       /\ network' = network \ {msg}
       /\ UNCHANGED vars
    \/ /\ msg.term = currentTerm[i]
       /\ network' = network \ {msg}
       /\ \/ HandleRequestVote(msg)
          \/ HandleRequestVoteResponse(msg)
          \/ HandleAppendEntries(msg)
          \/ HandleAppendEntriesResponse(msg)
          \/ HandleHeartbeat(msg)
          \/ HandleHeartbeatResponse(msg)
          \/ HandleTransferLeader(msg)
          \/ HandleTimeoutNow(msg)

HandleRequestVote(msg) ==
    /\ msg.type \in {MsgVote, MsgPreVote}
    /\ LET i == msg.to
           grantVote == \/ votedFor[i] = DefaultVote \/ votedFor[i] = msg.from
                        \/ (msg.type = MsgPreVote /\ msg.term > currentTerm[i])
    IN
    /\ state[i] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ grantVote
    /\ IsUpToDate(log[i], msg.index, msg.logTerm)
    /\ LET respType == IF msg.type = MsgVote THEN MsgVoteResp ELSE MsgPreVoteResp
           resp == [type |-> respType, to |-> msg.from, from |-> i, term |-> msg.term,
                    logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                    reject |-> FALSE, rejectHint |-> 0]
       IN network' = network \cup {resp}
    /\ IF msg.type = MsgVote
       THEN /\ votedFor' = [votedFor EXCEPT ![i] = msg.from]
            /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
       ELSE UNCHANGED <<votedFor, electionElapsed>>
    /\ UNCHANGED <<state, currentTerm, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader, votesGranted, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive>>

HandleRequestVoteResponse(msg) ==
    /\ msg.type \in {MsgVoteResp, MsgPreVoteResp}
    /\ LET i == msg.to
           myState == IF msg.type = MsgVoteResp THEN StateCandidate ELSE StatePreCandidate
    IN
    /\ state[i] = myState
    /\ \/ /\ msg.reject = FALSE
          /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {msg.from}]
          /\ IF Cardinality(votesGranted'[i]) >= Quorum
             THEN IF state[i] = StatePreCandidate
                  THEN /\ BecomeCandidate(i, i)
                       /\ LET term == currentTerm'[i]
                              lastIdx == LastLogIndex(log[i])
                              lastTerm == LastLogTerm(log[i])
                              req(j) == [type |-> MsgVote, to |-> j, from |-> i, term |-> term,
                                         logTerm |-> lastTerm, index |-> lastIdx, entries |-> <<>>,
                                         commit |-> 0, reject |-> FALSE, rejectHint |-> 0]
                          IN network' = network \cup {req(j) : j \in Server \ {i}}
                  ELSE /\ BecomeLeader(i, i)
                       /\ LET newEntry == [term |-> currentTerm[i], value |-> "noop", index |-> LastLogIndex(log[i]) + 1, type |-> "Normal"]
                          IN log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
                       /\ UNCHANGED <<network>>
             ELSE UNCHANGED <<state, currentTerm, votedFor, leader, leadTransferee, log, network>>
          /\ UNCHANGED <<commitIndex, appliedIndex, nextIndex, matchIndex, electionElapsed, heartbeatElapsed, randomizedElectionTimeout>>
       \/ /\ msg.reject = TRUE
          /\ BecomeFollower(i, i, currentTerm[i], DefaultVote)
          /\ UNCHANGED <<votesGranted, log, network>>

HandleAppendEntries(msg) ==
    /\ msg.type = MsgApp
    /\ LET i == msg.to
    IN
    /\ state[i] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ BecomeFollower(i, i, msg.term, msg.from)
    /\ LET prevLogTerm == TermAt(log[i], msg.index)
       IN \/ /\ msg.index > LastLogIndex(log[i]) \/ prevLogTerm # msg.logTerm
             /\ LET resp == [type |-> MsgAppResp, to |-> msg.from, from |-> i, term |-> currentTerm[i],
                             logTerm |-> 0, index |-> msg.index, entries |-> <<>>, commit |-> 0,
                             reject |-> TRUE, rejectHint |-> LastLogIndex(log[i])]
                IN network' = network \cup {resp}
             /\ UNCHANGED <<log, commitIndex>>
          \/ /\ prevLogTerm = msg.logTerm
             /\ LET newLog == Append(SubSeq(log[i], 1, msg.index), msg.entries)
                IN log' = [log EXCEPT ![i] = newLog]
             /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], Min({msg.commit, LastLogIndex(newLog)})})]
             /\ LET resp == [type |-> MsgAppResp, to |-> msg.from, from |-> i, term |-> currentTerm[i],
                             logTerm |-> 0, index |-> LastLogIndex(newLog), entries |-> <<>>, commit |-> 0,
                             reject |-> FALSE, rejectHint |-> 0]
                IN network' = network \cup {resp}
    /\ UNCHANGED <<appliedIndex, nextIndex, matchIndex, votesGranted, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive>>

HandleAppendEntriesResponse(msg) ==
    /\ msg.type = MsgAppResp
    /\ LET i == msg.to
           j == msg.from
    IN
    /\ state[i] = StateLeader
    /\ \/ /\ msg.reject = FALSE
          /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![j] = msg.index + 1]]
          /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![j] = msg.index]]
          /\ recentActive' = [recentActive EXCEPT ![j] = TRUE]
          /\ IF leadTransferee[i] = j /\ matchIndex'[i][j] = LastLogIndex(log[i])
             THEN LET timeoutMsg == [type |-> MsgTimeoutNow, to |-> j, from |-> i, term |-> currentTerm[i],
                                     logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                                     reject |-> FALSE, rejectHint |-> 0]
                  IN network' = network \cup {timeoutMsg}
             ELSE UNCHANGED <<network>>
          /\ UNCHANGED <<log, commitIndex, appliedIndex, state, currentTerm, votedFor, leader, votesGranted, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, leadTransferee>>
       \/ /\ msg.reject = TRUE
          /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![j] = Max({1, msg.rejectHint + 1})]]
          /\ UNCHANGED <<matchIndex, recentActive, log, commitIndex, appliedIndex, state, currentTerm, votedFor, leader, votesGranted, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, network>>

HandleHeartbeat(msg) ==
    /\ msg.type = MsgHeartbeat
    /\ LET i == msg.to
    IN
    /\ state[i] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ BecomeFollower(i, i, msg.term, msg.from)
    /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], msg.commit})]
    /\ LET resp == [type |-> MsgHeartbeatResp, to |-> msg.from, from |-> i, term |-> currentTerm[i],
                    logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                    reject |-> FALSE, rejectHint |-> 0]
       IN network' = network \cup {resp}
    /\ UNCHANGED <<log, appliedIndex, nextIndex, matchIndex, votesGranted, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive>>

HandleHeartbeatResponse(msg) ==
    /\ msg.type = MsgHeartbeatResp
    /\ LET i == msg.to
           j == msg.from
    IN
    /\ state[i] = StateLeader
    /\ recentActive' = [recentActive EXCEPT ![j] = TRUE]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader, votesGranted, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, network>>

HandleTransferLeader(msg) ==
    /\ msg.type = MsgTransferLeader
    /\ LET i == msg.to
    IN
    /\ state[i] = StateLeader
    /\ leadTransferee' = [leadTransferee EXCEPT ![i] = msg.from]
    /\ electionElapsed' = [electionElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader, votesGranted, heartbeatElapsed, randomizedElectionTimeout, recentActive, network>>

HandleTimeoutNow(msg) ==
    /\ msg.type = MsgTimeoutNow
    /\ LET i == msg.to
    IN
    /\ state[i] \in {StateFollower, StateCandidate}
    /\ BecomeCandidate(i, i)
    /\ LET term == currentTerm'[i]
           lastIdx == LastLogIndex(log[i])
           lastTerm == LastLogTerm(log[i])
           req(j) == [type |-> MsgVote, to |-> j, from |-> i, term |-> term,
                      logTerm |-> lastTerm, index |-> lastIdx, entries |-> <<>>,
                      commit |-> 0, reject |-> FALSE, rejectHint |-> 0]
       IN network' = network \cup {req(j) : j \in Server \ {i}}
    /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive>>

\* A leader advances its commit index.
UpdateCommitIndex(i) ==
    /\ state[i] = StateLeader
    /\ LET
        \* Find the highest index N such that a quorum of followers has matchIndex >= N
        \* and log[i][N].term = currentTerm[i].
        PossibleCommits == {
            n \in 1..LastLogIndex(log[i]) :
                /\ TermAt(log[i], n) = currentTerm[i]
                /\ Cardinality({j \in Server : matchIndex[i][j] >= n}) >= Quorum
        }
        NewCommitIndex == IF PossibleCommits = {} THEN commitIndex[i] ELSE Max(PossibleCommits)
       IN
    /\ NewCommitIndex > commitIndex[i]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = NewCommitIndex]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, appliedIndex, nextIndex, matchIndex, leader, votesGranted, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive, network>>

\* A server applies a committed entry to its state machine.
Apply(i) ==
    /\ commitIndex[i] > appliedIndex[i]
    /\ appliedIndex' = [appliedIndex EXCEPT ![i] = appliedIndex[i] + 1]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex, leader, votesGranted, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, recentActive, network>>

Next ==
    \/ \E i \in Server, v \in Value : ClientRequest(i, v)
    \/ \E i \in Server : Tick(i)
    \/ \E i \in Server : Timeout(i)
    \/ \E i \in Server : HeartbeatTimeout(i)
    \/ \E i \in Server : CheckQuorum(i)
    \/ \E i, j \in Server : SendAppendEntries(i, j)
    \/ \E msg \in network : Receive(msg)
    \/ \E i \in Server : UpdateCommitIndex(i)
    \/ \E i \in Server : Apply(i)

Spec == Init /\ [][Next]_vars

\* Invariants and Properties

TypeOK ==
    /\ state \in [Server -> RaftStates]
    /\ currentTerm \in [Server -> Nat]
    /\ votedFor \in [Server -> Server \cup {DefaultVote}]
    /\ \A i \in Server : log[i] \in Seq([term: Nat, value: Value, index: Nat, type: STRING])
    /\ commitIndex \in [Server -> Nat]
    /\ appliedIndex \in [Server -> Nat]
    /\ network \subseteq
        [type: MessageTypes, to: Server, from: Server, term: Nat, logTerm: Nat, index: Nat,
         entries: Seq(log[CHOOSE i \in Server]), commit: Nat, reject: BOOLEAN, rejectHint: Nat]

LeaderElectionSafety ==
    \A t \in {currentTerm[i] : i \in Server} :
        Cardinality({i \in Server : state[i] = StateLeader /\ currentTerm[i] = t}) <= 1

LogMatching ==
    \A i, j \in Server :
        \A idx \in 1..Min({Len(log[i]), Len(log[j])}) :
            log[i][idx].term = log[j][idx].term => log[i][idx] = log[j][idx]

LeaderCompleteness ==
    \A t \in {currentTerm[i] : i \in Server} :
        \A i \in Server :
            IF state[i] = StateLeader /\ currentTerm[i] = t
            THEN \A t_prev \in {currentTerm[j] : j \in Server} :
                    \A j \in Server :
                        IF state[j] = StateLeader /\ currentTerm[j] = t_prev /\ t_prev < t
                        THEN \A entry \in DOMAIN log[j] :
                                IF log[j][entry].index <= commitIndex[j]
                                THEN \E entry_i \in DOMAIN log[i] : log[i][entry_i] = log[j][entry]

StateConsistency ==
    \A i \in Server :
        (state[i] = StateLeader) => (leader[i] = i)

CommittedLogsArePrefixes ==
    \A i, j \in Server :
        LET ci == commitIndex[i]
            cj == commitIndex[j]
        IN \A idx \in 1..Min({ci, cj}) :
            log[i][idx] = log[j][idx]

CommittedLogsAreInLeaderLogs ==
    \A i \in Server :
        IF state[i] = StateLeader
        THEN \A j \in Server :
                \A idx \in 1..commitIndex[j] :
                    \E l_idx \in DOMAIN log[i] : log[i][l_idx] = log[j][idx]

====
