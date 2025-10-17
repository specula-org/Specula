---- MODULE etcdraft ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    \* @type: Set(Str);
    Servers,      \* The set of server IDs (nodes).
    \* @type: Set(Str);
    Clients,      \* The set of client IDs.
    \* @type: Str;
    Data,         \* The set of possible values for the key-value store.
    \* @type: Str;
    Key,          \* The set of possible keys for the key-value store.
    \* @type: Int;
    ElectionTimeout,
    \* @type: Int;
    HeartbeatTimeout

ASSUME \A s \in Servers: s /= "None"
ASSUME HeartbeatTimeout < ElectionTimeout

\* A distinguished value for "no one"
None == "None"

\* Server states from the Go code
State_Follower      == "StateFollower"
State_Candidate     == "StateCandidate"
State_Leader        == "StateLeader"
State_PreCandidate  == "StatePreCandidate"
ServerStates == {State_Follower, State_Candidate, State_Leader, State_PreCandidate}

\* Message types from raftpb
MsgTypes == {
    "MsgHup", "MsgBeat", "MsgProp", "MsgApp", "MsgAppResp", "MsgVote", "MsgVoteResp",
    "MsgSnap", "MsgHeartbeat", "MsgHeartbeatResp", "MsgUnreachable", "MsgSnapStatus",
    "MsgCheckQuorum", "MsgTransferLeader", "MsgTimeoutNow", "MsgReadIndex", "MsgReadIndexResp",
    "MsgPreVote", "MsgPreVoteResp"
}

\* Entry types from raftpb
EntryTypes == {"EntryNormal", "EntryConfChange"}

\* Campaign types from the Go code
CampaignTypes == {"CampaignPreElection", "CampaignElection", "CampaignTransfer"}

VARIABLES
    \* Per-server state variables, matching the 'raft' struct
    \* @type: [ oneIn(Servers) -> Str ];
    state,              \* Server state (Follower, Candidate, etc.)
    \* @type: [ oneIn(Servers) -> Int ];
    currentTerm,        \* Latest term server has seen
    \* @type: [ oneIn(Servers) -> oneIn(Servers \union {None}) ];
    votedFor,           \* Candidate that received vote in current term
    \* @type: [ oneIn(Servers) -> Seq([term: Int, index: Int, data: Str, type: Str]) ];
    log,                \* Log entries; each entry has term, index, data, and type
    \* @type: [ oneIn(Servers) -> Int ];
    commitIndex,        \* Index of highest log entry known to be committed
    \* @type: [ oneIn(Servers) -> Int ];
    appliedIndex,       \* Index of highest log entry applied to state machine
    \* @type: [ oneIn(Servers) -> oneIn(Servers \union {None}) ];
    leader,             \* The node's belief about the current leader
    \* @type: [ oneIn(Servers) -> Int ];
    electionElapsed,    \* Ticks since last election timeout reset
    \* @type: [ oneIn(Servers) -> Int ];
    heartbeatElapsed,   \* Ticks since last heartbeat
    \* @type: [ oneIn(Servers) -> Int ];
    randomizedElectionTimeout, \* Randomized timeout for each server

    \* Leader-specific state
    \* @type: [ oneIn(Servers) -> [ oneIn(Servers) -> Int ] ];
    nextIndex,          \* For each server, index of the next log entry to send to that server
    \* @type: [ oneIn(Servers) -> [ oneIn(Servers) -> Int ] ];
    matchIndex,         \* For each server, index of highest log entry known to be replicated on server
    \* @type: [ oneIn(Servers) -> oneIn(Servers \union {None}) ];
    leadTransferee,     \* ID of the leader transfer target

    \* Configuration state
    \* @type: [ oneIn(Servers) -> Set(Str) ];
    voters,             \* The set of voting members in the cluster, as seen by each server
    \* @type: [ oneIn(Servers) -> Set(Str) ];
    learners,           \* The set of non-voting members
    \* @type: [ oneIn(Servers) -> Int ];
    pendingConfIndex,   \* Index of a pending configuration change

    \* The network, modeled as a set of messages
    \* @type: Set([type: Str, from: oneIn(Servers \union Clients), to: oneIn(Servers), term: Int, logTerm: Int, index: Int, entries: Seq(Any), commit: Int, reject: BOOLEAN, context: Str]);
    network,

    \* The key-value store state machine for each server
    \* @type: [ oneIn(Servers) -> [ oneIn(Key) -> oneIn(Data) ] ];
    kvStore,

    \* Client-facing state
    \* @type: [ oneIn(Clients) -> [reqId: Int, status: Str, value: Str] ];
    clientResponses

\* Helper functions
LastLogIndex(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].index
LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term
GetEntry(l, idx) == CHOOSE e \in DOMAIN l: l[e].index = idx
Quorum(cfg) == (Cardinality(cfg) \div 2) + 1
IsVoter(s, cfg) == s \in cfg
IsLearner(s, lcfg) == s \in lcfg
Promotable(s, vcfg, lcfg) == s \in vcfg /\ s \notin lcfg

\* Check if a candidate's log is "at least as up-to-date"
IsUpToDate(candidateLog, localLog) ==
    LET candLastTerm == LastLogTerm(candidateLog)
        candLastIndex == LastLogIndex(candidateLog)
        localLastTerm == LastLogTerm(localLog)
        localLastIndex == LastLogIndex(localLog)
    IN (candLastTerm > localLastTerm) \/
       (candLastTerm = localLastTerm /\ candLastIndex >= localLastIndex)

\* State transition helpers, mirroring becomeFollower, becomeCandidate, etc.
BecomeFollower(s, term, newLeader) ==
    /\ state' = [state EXCEPT ![s] = State_Follower]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = None]
    /\ leader' = [leader EXCEPT ![s] = newLeader]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = None]
    /\ UNCHANGED << heartbeatElapsed, randomizedElectionTimeout, log, commitIndex, appliedIndex, nextIndex, matchIndex, voters, learners, pendingConfIndex, network, kvStore, clientResponses >>

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = State_PreCandidate]
    /\ leader' = [leader EXCEPT ![s] = None]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ UNCHANGED << currentTerm, votedFor, heartbeatElapsed, randomizedElectionTimeout, log, commitIndex, appliedIndex, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, network, kvStore, clientResponses >>

BecomeCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = State_Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ leader' = [leader EXCEPT ![s] = None]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ UNCHANGED << heartbeatElapsed, randomizedElectionTimeout, log, commitIndex, appliedIndex, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, network, kvStore, clientResponses >>

BecomeLeader(s) ==
    /\ state' = [state EXCEPT ![s] = State_Leader]
    /\ leader' = [leader EXCEPT ![s] = s]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = None]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(log[s]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0] WITH [s] |-> LastLogIndex(log[s])]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![s] = LastLogIndex(log[s])]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ UNCHANGED << currentTerm, votedFor, electionElapsed, randomizedElectionTimeout, log, commitIndex, appliedIndex, voters, learners, network, kvStore, clientResponses >>

\* Initial state of the system
Init ==
    /\ state = [s \in Servers |-> State_Follower]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> None]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ appliedIndex = [s \in Servers |-> 0]
    /\ leader = [s \in Servers |-> None]
    /\ electionElapsed = [s \in Servers |-> 0]
    /\ heartbeatElapsed = [s \in Servers |-> 0]
    /\ randomizedElectionTimeout = [s \in Servers |-> ElectionTimeout] \* Simplified, could be random
    /\ nextIndex = [s \in Servers |-> [p \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [p \in Servers |-> 0]]
    /\ leadTransferee = [s \in Servers |-> None]
    /\ voters = [s \in Servers |-> Servers]
    /\ learners = [s \in Servers |-> {}]
    /\ pendingConfIndex = [s \in Servers |-> 0]
    /\ network = {}
    /\ kvStore = [s \in Servers |-> [k \in Key |-> ""]]
    /\ clientResponses = [c \in Clients |-> [reqId |-> 0, status |-> "None", value |-> ""]]

\* Actions that can occur in the system

\* A client sends a proposal to a server
ClientRequest(c, s, k, v, reqId) ==
    /\ clientResponses[c].reqId < reqId
    /\ LET msg = [type |-> "MsgProp", from |-> c, to |-> s, term |-> 0,
                  entries |-> <<[term |-> 0, index |-> 0, data |-> k, type |-> v]>>,
                  logTerm |-> 0, index |-> 0, commit |-> 0, reject |-> FALSE, context |-> reqId]
    IN network' = network \cup {msg}
    /\ clientResponses' = [clientResponses EXCEPT ![c].reqId = reqId, ![c].status = "InProgress"]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore >>

\* Time passes, timers are incremented
Tick ==
    /\ \E s \in Servers:
        (state[s] /= State_Leader /\ electionElapsed[s] < 2*ElectionTimeout) \/
        (state[s] = State_Leader /\ heartbeatElapsed[s] < ElectionTimeout)
    /\ electionElapsed' = [s \in Servers |->
                            IF state[s] /= State_Leader THEN electionElapsed[s] + 1
                            ELSE electionElapsed[s]]
    /\ heartbeatElapsed' = [s \in Servers |->
                             IF state[s] = State_Leader THEN heartbeatElapsed[s] + 1
                             ELSE heartbeatElapsed[s]]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, network, kvStore, clientResponses >>

\* An election times out for a follower or candidate
ElectionTimeout(s) ==
    /\ state[s] \in {State_Follower, State_Candidate, State_PreCandidate}
    /\ electionElapsed[s] >= randomizedElectionTimeout[s]
    /\ Promotable(s, voters[s], learners[s])
    /\ LET msg = [type |-> "MsgHup", from |-> s, to |-> s, term |-> 0,
                  entries |-> << >>, logTerm |-> 0, index |-> 0, commit |-> 0, reject |-> FALSE, context |-> ""]
    IN network' = network \cup {msg}
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

\* A leader's heartbeat timer fires
HeartbeatTimeout(s) ==
    /\ state[s] = State_Leader
    /\ heartbeatElapsed[s] >= HeartbeatTimeout
    /\ LET msg = [type |-> "MsgBeat", from |-> s, to |-> s, term |-> 0,
                  entries |-> << >>, logTerm |-> 0, index |-> 0, commit |-> 0, reject |-> FALSE, context |-> ""]
    IN network' = network \cup {msg}
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

\* A message is delivered from the network
Receive(msg) ==
    LET s == msg.to
    IN
    \* Message with a higher term causes the receiver to become a follower
    IF msg.term > currentTerm[s] THEN
        /\ msg.type \notin {"MsgPreVote", "MsgPreVoteResp"} \* Pre-vote does not change term
        /\ BecomeFollower(s, msg.term, IF msg.type \in {"MsgApp", "MsgHeartbeat"} THEN msg.from ELSE None)
        /\ network' = network \ {msg}
        /\ UNCHANGED << kvStore, clientResponses >>

    \* Message with a lower term is rejected
    ELSE IF msg.term < currentTerm[s] THEN
        /\ network' = network \ {msg}
        /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

    \* Message with the current term is processed based on state
    ELSE CASE msg.type = "MsgHup" ->
            \* Start a pre-election
            /\ BecomePreCandidate(s)
            /\ LET voteMsg = [type |-> "MsgPreVote", from |-> s, to |-> p,
                              term |-> currentTerm[s] + 1,
                              logTerm |-> LastLogTerm(log[s]), index |-> LastLogIndex(log[s]),
                              entries |-> << >>, commit |-> 0, reject |-> FALSE, context |-> ""]
            IN network' = (network \ {msg}) \cup { [voteMsg EXCEPT !.to = p] : p \in voters[s] }
            /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, appliedIndex, leader, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgBeat" ->
            /\ state[s] = State_Leader
            /\ LET heartbeat = [type |-> "MsgHeartbeat", from |-> s, to |-> p,
                                term |-> currentTerm[s], commit |-> commitIndex[s],
                                logTerm |-> 0, index |-> 0, entries |-> << >>, reject |-> FALSE, context |-> ""]
            IN network' = (network \ {msg}) \cup { [heartbeat EXCEPT !.to = p] : p \in voters[s] \ {s} }
            /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgProp" ->
            IF state[s] = State_Leader THEN
                /\ leadTransferee[s] = None
                /\ LET newEntry = [term |-> currentTerm[s],
                                   index |-> LastLogIndex(log[s]) + 1,
                                   data |-> msg.entries[1].data,
                                   type |-> msg.entries[1].type]
                IN log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
                /\ network' = network \ {msg}
                /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>
            ELSE
                /\ leader[s] /= None
                /\ LET fwdMsg = [msg EXCEPT !.to = leader[s]]
                IN network' = (network \ {msg}) \cup {fwdMsg}
                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgPreVote" ->
            /\ LET voteGranted = (votedFor[s] = None \/ votedFor[s] = msg.from) /\
                                 IsUpToDate(msg, log[s])
            /\ LET resp = [type |-> "MsgPreVoteResp", from |-> s, to |-> msg.from,
                           term |-> msg.term, reject |-> ~voteGranted,
                           logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0, context |-> ""]
            IN network' = (network \ {msg}) \cup {resp}
            /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgVote" ->
            /\ LET voteGranted = (votedFor[s] = None \/ votedFor[s] = msg.from) /\
                                 IsUpToDate(msg, log[s])
            /\ IF voteGranted THEN
                votedFor' = [votedFor EXCEPT ![s] = msg.from]
               ELSE
                votedFor' = votedFor
            /\ LET resp = [type |-> "MsgVoteResp", from |-> s, to |-> msg.from,
                           term |-> currentTerm[s], reject |-> ~voteGranted,
                           logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0, context |-> ""]
            IN network' = (network \ {msg}) \cup {resp}
            /\ UNCHANGED << state, currentTerm, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgPreVoteResp" ->
            /\ state[s] = State_PreCandidate
            /\ LET votes = {p \in voters[s] | \E m \in network: m.type = "MsgPreVoteResp" /\ m.from = p /\ m.to = s /\ m.term = currentTerm[s]+1 /\ ~m.reject}
            /\ IF Cardinality(votes) + 1 >= Quorum(voters[s]) THEN
                \* Won pre-vote, start real election
                /\ BecomeCandidate(s)
                /\ LET voteMsg = [type |-> "MsgVote", from |-> s, to |-> p,
                                  term |-> currentTerm[s] + 1,
                                  logTerm |-> LastLogTerm(log[s]), index |-> LastLogIndex(log[s]),
                                  entries |-> << >>, commit |-> 0, reject |-> FALSE, context |-> ""]
                IN network' = (network \ {msg}) \cup { [voteMsg EXCEPT !.to = p] : p \in voters[s] }
            ELSE
                /\ network' = network \ {msg}
                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgVoteResp" ->
            /\ state[s] = State_Candidate
            /\ LET votes = {p \in voters[s] | \E m \in network: m.type = "MsgVoteResp" /\ m.from = p /\ m.to = s /\ m.term = currentTerm[s] /\ ~m.reject} \cup {s}
            /\ IF Cardinality(votes) >= Quorum(voters[s]) THEN
                \* Won election, become leader
                /\ BecomeLeader(s)
                /\ LET newEntry = [term |-> currentTerm[s], index |-> LastLogIndex(log[s]) + 1, data |-> "noop", type |-> "EntryNormal"]
                /\ log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
                /\ network' = network \ {msg}
            ELSE
                /\ network' = network \ {msg}
                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgApp" ->
            /\ state[s] \in {State_Follower, State_Candidate, State_PreCandidate}
            /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
            /\ leader' = [leader EXCEPT ![s] = msg.from]
            /\ LET logOK = msg.index = 0 \/
                           (msg.index <= LastLogIndex(log[s]) /\ log[s][GetEntry(log[s], msg.index)].term = msg.logTerm)
            /\ IF logOK THEN
                /\ LET newEntries = SubSeq(msg.entries, 1, Len(msg.entries))
                /\ LET conflictIndex = CHOOSE i \in 1..Len(newEntries):
                                        LET entry = newEntries[i]
                                        IN entry.index > LastLogIndex(log[s]) \/ log[s][GetEntry(log[s], entry.index)].term /= entry.term
                                     ELSE Len(newEntries) + 1
                /\ log' = [log EXCEPT ![s] = Append(SubSeq(log[s], 1, msg.index), SubSeq(newEntries, 1, conflictIndex - 1))]
                /\ IF msg.commit > commitIndex[s] THEN
                    commitIndex' = [commitIndex EXCEPT ![s] = min(msg.commit, LastLogIndex(log'[s]))]
                   ELSE
                    commitIndex' = commitIndex
                /\ LET resp = [type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                               term |-> currentTerm[s], reject |-> FALSE, index |-> LastLogIndex(log'[s]),
                               logTerm |-> 0, entries |-> << >>, commit |-> 0, context |-> ""]
                IN network' = (network \ {msg}) \cup {resp}
            ELSE
                /\ LET resp = [type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                               term |-> currentTerm[s], reject |-> TRUE, index |-> msg.index,
                               logTerm |-> 0, entries |-> << >>, commit |-> 0, context |-> ""]
                IN network' = (network \ {msg}) \cup {resp}
                /\ UNCHANGED << log, commitIndex >>
            /\ UNCHANGED << state, currentTerm, votedFor, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgAppResp" ->
            /\ state[s] = State_Leader
            /\ IF msg.reject = FALSE THEN
                /\ matchIndex' = [matchIndex EXCEPT ![s][msg.from] = msg.index]
                /\ nextIndex' = [nextIndex EXCEPT ![s][msg.from] = msg.index + 1]
            ELSE
                /\ nextIndex' = [nextIndex EXCEPT ![s][msg.from] = max(1, nextIndex[s][msg.from] - 1)]
                /\ UNCHANGED matchIndex
            /\ network' = network \ {msg}
            /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgHeartbeat" ->
            /\ state[s] \in {State_Follower, State_Candidate, State_PreCandidate}
            /\ leader' = [leader EXCEPT ![s] = msg.from]
            /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
            /\ IF msg.commit > commitIndex[s] THEN
                commitIndex' = [commitIndex EXCEPT ![s] = min(msg.commit, LastLogIndex(log[s]))]
               ELSE
                commitIndex' = commitIndex
            /\ LET resp = [type |-> "MsgHeartbeatResp", from |-> s, to |-> msg.from,
                           term |-> currentTerm[s], context |-> msg.context,
                           logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0, reject |-> FALSE]
            IN network' = (network \ {msg}) \cup {resp}
            /\ UNCHANGED << state, currentTerm, votedFor, log, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgTransferLeader" ->
            IF state[s] = State_Leader THEN
                /\ leadTransferee' = [leadTransferee EXCEPT ![s] = msg.from]
                /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
                /\ network' = network \ {msg}
            ELSE
                /\ leader[s] /= None
                /\ LET fwdMsg = [msg EXCEPT !.to = leader[s]]
                IN network' = (network \ {msg}) \cup {fwdMsg}
                /\ UNCHANGED << leadTransferee, electionElapsed >>
            /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, voters, learners, pendingConfIndex, kvStore, clientResponses >>

\* Leader sends AppendEntries to a follower
LeaderSendAppend(s, peer) ==
    /\ state[s] = State_Leader
    /\ peer \in voters[s] \ {s}
    /\ LastLogIndex(log[s]) >= nextIndex[s][peer]
    /\ LET prevIndex = nextIndex[s][peer] - 1
    /\ LET prevTerm = IF prevIndex > 0 THEN log[s][GetEntry(log[s], prevIndex)].term ELSE 0
    /\ LET entriesToSend = SubSeq(log[s], GetEntry(log[s], prevIndex + 1), Len(log[s]))
    /\ LET msg = [type |-> "MsgApp", from |-> s, to |-> peer, term |-> currentTerm[s],
                  logTerm |-> prevTerm, index |-> prevIndex, entries |-> entriesToSend,
                  commit |-> commitIndex[s], reject |-> FALSE, context |-> ""]
    IN network' = network \cup {msg}
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

\* Leader advances its commit index
LeaderAdvanceCommitIndex(s) ==
    /\ state[s] = State_Leader
    /\ \E n \in (commitIndex[s]+1)..LastLogIndex(log[s]):
        /\ log[s][GetEntry(log[s], n)].term = currentTerm[s]
        /\ Cardinality({p \in voters[s] | matchIndex[s][p] >= n}) >= Quorum(voters[s])
    /\ LET newCommitIndex = Max({n \in (commitIndex[s]+1)..LastLogIndex(log[s]) |
                                    log[s][GetEntry(log[s], n)].term = currentTerm[s] /\
                                    Cardinality({p \in voters[s] | matchIndex[s][p] >= n}) >= Quorum(voters[s])})
    IN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
    /\ UNCHANGED << state, currentTerm, votedFor, log, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, network, kvStore, clientResponses >>

\* A server applies a committed entry to its state machine
Apply(s) ==
    /\ commitIndex[s] > appliedIndex[s]
    /\ LET i = appliedIndex[s] + 1
    /\ LET entry = log[s][GetEntry(log[s], i)]
    /\ appliedIndex' = [appliedIndex EXCEPT ![s] = i]
    /\ IF entry.type = "EntryNormal" THEN
        /\ kvStore' = [kvStore EXCEPT ![s][entry.data] = entry.type]
        /\ UNCHANGED << voters, learners, pendingConfIndex >>
       ELSE \* EntryConfChange
        /\ LET newVoters = {p \in Servers | "some logic to parse entry.data"}
        /\ LET newLearners = {p \in Servers | "some logic to parse entry.data"}
        /\ voters' = [voters EXCEPT ![s] = newVoters]
        /\ learners' = [learners EXCEPT ![s] = newLearners]
        /\ UNCHANGED << kvStore, pendingConfIndex >>
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, network, clientResponses >>

\* A message is dropped from the network (simulating network partition/loss)
DropMessage(msg) ==
    /\ msg \in network
    /\ network' = network \ {msg}
    /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

Next ==
    \/ \E c \in Clients, s \in Servers, k \in Key, v \in Data, r \in 1..100: ClientRequest(c, s, k, v, r)
    \/ Tick
    \/ \E s \in Servers: ElectionTimeout(s)
    \/ \E s \in Servers: HeartbeatTimeout(s)
    \/ \E msg \in network: Receive(msg)
    \/ \E s \in Servers, p \in Servers: LeaderSendAppend(s, p)
    \/ \E s \in Servers: LeaderAdvanceCommitIndex(s)
    \/ \E s \in Servers: Apply(s)
    \/ \E msg \in network: DropMessage(msg)

Spec == Init /\ [][Next]_vars

\* Invariants and properties

\* At most one leader can exist in any given term.
LeaderSafety ==
    \A t \in 1..Max(DOMAIN currentTerm):
        Cardinality({s \in Servers | state[s] = State_Leader /\ currentTerm[s] = t}) <= 1

\* All logs agree on committed entries.
LogMatching ==
    \A s1, s2 \in Servers:
        \A i \in 1..min(Len(log[s1]), Len(log[s2])):
            (log[s1][i].term = log[s2][i].term) => (log[s1][i] = log[s2][i])

\* If an entry is committed, it is present in the logs of all leaders of higher terms.
LeaderCompleteness ==
    \A i \in 1..Len(log[s1]):
        \A s1 \in Servers:
            (i <= commitIndex[s1]) =>
                (\A t \in (log[s1][i].term+1)..Max(DOMAIN currentTerm):
                    \A s2 \in Servers:
                        (state[s2] = State_Leader /\ currentTerm[s2] = t) => (Len(log[s2]) >= i /\ log[s2][i] = log[s1][i]))

\* Entries that are applied must first be committed.
AppliedIsCommitted ==
    \A s \in Servers: appliedIndex[s] <= commitIndex[s]

\* All state machines apply the same sequence of commands.
StateMachineSafety ==
    \A s1, s2 \in Servers:
        \A i \in 1..min(appliedIndex[s1], appliedIndex[s2]):
            log[s1][GetEntry(log[s1], i)] = log[s2][GetEntry(log[s2], i)]

\* Type invariant for model checking
TypeOK ==
    /\ \A s \in Servers:
        /\ state[s] \in ServerStates
        /\ currentTerm[s] \in Int
        /\ votedFor[s] \in Servers \union {None}
        /\ commitIndex[s] \in Int
        /\ appliedIndex[s] \in Int
        /\ leader[s] \in Servers \union {None}
        /\ electionElapsed[s] \in Int
        /\ heartbeatElapsed[s] \in Int
        /\ leadTransferee[s] \in Servers \union {None}
        /\ voters[s] \subseteq Servers
        /\ learners[s] \subseteq Servers
    /\ network \subseteq [type: MsgTypes, from: Servers \union Clients, to: Servers, term: Int, logTerm: Int, index: Int, entries: Seq(Any), commit: Int, reject: BOOLEAN, context: Any]

vars == << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
           electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
           nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex,
           network, kvStore, clientResponses >>

====