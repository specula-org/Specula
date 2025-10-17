---- MODULE etcdraft ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    \* @type: Set(Str);
    Servers,      \* The set of server IDs (nodes).
    \* @type: Set(Str);
    Clients,      \* The set of client IDs.
    \* The set of possible values for the key-value store.
    Data,
    \* The set of possible keys for the key-value store.
    Key,
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
EntryTypes == {"EntryNormal"}

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
    \* @type: [ oneIn(Servers) -> Seq([term: Int, index: Int, op: Any, entryType: Str]) ];
    log,                \* Log entries; each entry has term, index, op, and type
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

vars == << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader,
           electionElapsed, heartbeatElapsed, randomizedElectionTimeout,
           nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex,
           network, kvStore, clientResponses >>

\* Helper functions
LastLogIndex(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].index
LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term
GetEntry(l, idx) == CHOOSE e \in DOMAIN l: l[e].index = idx
GetLogEntry(l, idx) == CHOOSE e \in l: e.index = idx
Quorum(cfg) == (Cardinality(cfg) \div 2) + 1
IsVoter(s, cfg) == s \in cfg
IsLearner(s, lcfg) == s \in lcfg
Promotable(s, vcfg, lcfg) == s \in vcfg /\ s \notin lcfg
min(a,b) == IF a < b THEN a ELSE b
max(a,b) == IF a > b THEN a ELSE b

\* Check if a candidate's log is "at least as up-to-date"
IsUpToDate(candLastTerm, candLastIndex, localLog) ==
    LET localLastTerm == LastLogTerm(localLog)
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
    /\ LET msg == [type |-> "MsgProp", from |-> c, to |-> s, term |-> 0,
                   entries |-> <<[term |-> 0, index |-> 0, op |-> [key |-> k, val |-> v], entryType |-> "EntryNormal"]>>,
                   logTerm |-> 0, index |-> 0, commit |-> 0, reject |-> FALSE, context |-> reqId]
    IN /\ network' = network \cup {msg}
       /\ clientResponses' = [clientResponses EXCEPT ![c] = [clientResponses[c] EXCEPT !.reqId = reqId, !.status = "InProgress"]]
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
    /\ LET msg == [type |-> "MsgHup", from |-> s, to |-> s, term |-> 0,
                   entries |-> << >>, logTerm |-> 0, index |-> 0, commit |-> 0, reject |-> FALSE, context |-> ""]
    IN /\ network' = network \cup {msg}
       /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

\* A leader's heartbeat timer fires
HeartbeatTimeout(s) ==
    /\ state[s] = State_Leader
    /\ heartbeatElapsed[s] >= HeartbeatTimeout
    /\ LET msg == [type |-> "MsgBeat", from |-> s, to |-> s, term |-> 0,
                   entries |-> << >>, logTerm |-> 0, index |-> 0, commit |-> 0, reject |-> FALSE, context |-> ""]
    IN /\ network' = network \cup {msg}
       /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

\* A message is delivered from the network
Receive(msg) ==
    LET s == msg.to
    IN
    \* Message with a higher term causes the receiver to become a follower
    IF msg.term > currentTerm[s] THEN
        (   /\ msg.type \notin {"MsgPreVote", "MsgPreVoteResp"} \* Pre-vote does not change term
            /\ BecomeFollower(s, msg.term, IF msg.type \in {"MsgApp", "MsgHeartbeat"} THEN msg.from ELSE None)
            /\ network' = network \ {msg}
            /\ UNCHANGED << kvStore, clientResponses >>
        )
    \* Message with a lower term is rejected
    ELSE IF msg.term < currentTerm[s] THEN
        (   /\ network' = network \ {msg}
            /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>
        )
    \* Message with the current term is processed based on state
    ELSE CASE msg.type = "MsgHup" ->
            LET voteMsg == [type |-> "MsgPreVote", from |-> s, to |-> "dummy",
                            term |-> currentTerm[s] + 1,
                            logTerm |-> LastLogTerm(log[s]), index |-> LastLogIndex(log[s]),
                            entries |-> << >>, commit |-> 0, reject |-> FALSE, context |-> ""]
            IN /\ state' = [state EXCEPT ![s] = State_PreCandidate]
               /\ leader' = [leader EXCEPT ![s] = None]
               /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
               /\ network' = (network \ {msg}) \cup { [voteMsg EXCEPT !.to = p] : p \in voters[s] }
               /\ UNCHANGED << currentTerm, votedFor, log, commitIndex, appliedIndex, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgBeat" ->
            LET heartbeat == [type |-> "MsgHeartbeat", from |-> s, to |-> "dummy",
                              term |-> currentTerm[s], commit |-> commitIndex[s],
                              logTerm |-> 0, index |-> 0, entries |-> << >>, reject |-> FALSE, context |-> ""]
            IN /\ state[s] = State_Leader
               /\ network' = (network \ {msg}) \cup { [heartbeat EXCEPT !.to = p] : p \in voters[s] \ {s} }
               /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgProp" ->
            IF state[s] = State_Leader THEN
                LET newEntry == [term |-> currentTerm[s],
                                 index |-> LastLogIndex(log[s]) + 1,
                                 op |-> msg.entries[1].op,
                                 entryType |-> "EntryNormal"]
                IN /\ leadTransferee[s] = None
                   /\ log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
                   /\ network' = network \ {msg}
                   /\ UNCHANGED << state, currentTerm, votedFor, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>
            ELSE
                /\ leader[s] /= None
                /\ LET fwdMsg = [msg EXCEPT !.to = leader[s]]
                IN /\ network' = (network \ {msg}) \cup {fwdMsg}
                   /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgPreVote" ->
            LET voteGranted == IsUpToDate(msg.logTerm, msg.index, log[s])
                resp == [type |-> "MsgPreVoteResp", from |-> s, to |-> msg.from,
                         term |-> msg.term, reject |-> ~voteGranted,
                         logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0, context |-> ""]
            IN /\ network' = (network \ {msg}) \cup {resp}
               /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgVote" ->
            LET voteGranted == (votedFor[s] = None \/ votedFor[s] = msg.from) /\
                               IsUpToDate(msg.logTerm, msg.index, log[s])
                resp == [type |-> "MsgVoteResp", from |-> s, to |-> msg.from,
                         term |-> currentTerm[s], reject |-> ~voteGranted,
                         logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0, context |-> ""]
            IN /\ network' = (network \ {msg}) \cup {resp}
               /\ IF voteGranted THEN
                    /\ votedFor' = [votedFor EXCEPT ![s] = msg.from]
                    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
               ELSE
                    /\ UNCHANGED << votedFor, electionElapsed >>
               /\ UNCHANGED << state, currentTerm, log, commitIndex, appliedIndex, leader, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgPreVoteResp" ->
            LET votes == {p \in voters[s] | \E m \in network: m.type = "MsgPreVoteResp" /\ m.from = p /\ m.to = s /\ m.term = currentTerm[s]+1 /\ ~m.reject}
            IN /\ state[s] = State_PreCandidate
               /\ IF Cardinality(votes) + 1 >= Quorum(voters[s]) THEN
                   \* Won pre-vote, start real election
                   LET voteMsg == [type |-> "MsgVote", from |-> s, to |-> "dummy",
                                   term |-> currentTerm[s] + 1,
                                   logTerm |-> LastLogTerm(log[s]), index |-> LastLogIndex(log[s]),
                                   entries |-> << >>, commit |-> 0, reject |-> FALSE, context |-> ""]
                   IN /\ state' = [state EXCEPT ![s] = State_Candidate]
                      /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
                      /\ votedFor' = [votedFor EXCEPT ![s] = s]
                      /\ leader' = [leader EXCEPT ![s] = None]
                      /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
                      /\ network' = (network \ {msg}) \cup { [voteMsg EXCEPT !.to = p] : p \in voters[s] }
                      /\ UNCHANGED << heartbeatElapsed, randomizedElectionTimeout, log, commitIndex, appliedIndex, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>
                  ELSE
                      /\ network' = network \ {msg}
                      /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgVoteResp" ->
            LET votes == {p \in voters[s] | \E m \in network: m.type = "MsgVoteResp" /\ m.from = p /\ m.to = s /\ m.term = currentTerm[s] /\ ~m.reject} \cup {s}
            IN /\ state[s] = State_Candidate
               /\ IF Cardinality(votes) >= Quorum(voters[s]) THEN
                   \* Won election, become leader
                   LET newEntry == [term |-> currentTerm[s], index |-> LastLogIndex(log[s]) + 1, op |-> "noop", entryType |-> "EntryNormal"]
                       newLog == Append(log[s], newEntry)
                   IN /\ state' = [state EXCEPT ![s] = State_Leader]
                      /\ leader' = [leader EXCEPT ![s] = s]
                      /\ leadTransferee' = [leadTransferee EXCEPT ![s] = None]
                      /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(newLog) + 1]]
                      /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> IF p = s THEN LastLogIndex(newLog) ELSE 0]]
                      /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![s] = LastLogIndex(newLog)]
                      /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
                      /\ log' = [log EXCEPT ![s] = newLog]
                      /\ network' = network \ {msg}
                      /\ UNCHANGED << currentTerm, votedFor, electionElapsed, randomizedElectionTimeout, commitIndex, appliedIndex, voters, learners, kvStore, clientResponses >>
               ELSE
                   /\ network' = network \ {msg}
                   /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgApp" ->
            LET s == msg.to
                prevLogExists == \/ msg.index = 0
                                 \/ \E e \in log[s]: e.index = msg.index /\ e.term = msg.logTerm
            IN /\ state[s] \in {State_Follower, State_Candidate, State_PreCandidate}
               /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
               /\ leader' = [leader EXCEPT ![s] = msg.from]
               /\ IF prevLogExists THEN
                   LET conflictEntries == {entry \in msg.entries | \E e \in log[s]: e.index = entry.index /\ e.term /= entry.term}
                       logAfterTruncation == IF conflictEntries = {} THEN log[s]
                                             ELSE LET firstConflict = CHOOSE e \in conflictEntries: e.index = Min({ee.index | ee \in conflictEntries})
                                                      seqIdx = CHOOSE i \in DOMAIN log[s]: log[s][i].index = firstConflict.index
                                                  IN SubSeq(log[s], 1, seqIdx - 1)
                       lastIndex == LastLogIndex(logAfterTruncation)
                       entriesToAppend == << e \in msg.entries : e.index > lastIndex >>
                       newLog == Append(logAfterTruncation, entriesToAppend)
                       resp == [type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                                term |-> currentTerm[s], reject |-> FALSE, index |-> LastLogIndex(newLog),
                                logTerm |-> 0, entries |-> << >>, commit |-> 0, context |-> ""]
                   IN /\ log' = [log EXCEPT ![s] = newLog]
                      /\ IF msg.commit > commitIndex[s] THEN
                           commitIndex' = [commitIndex EXCEPT ![s] = min(msg.commit, LastLogIndex(newLog))]
                         ELSE
                           commitIndex' = commitIndex
                      /\ network' = (network \ {msg}) \cup {resp}
               ELSE
                   LET resp == [type |-> "MsgAppResp", from |-> s, to |-> msg.from,
                                term |-> currentTerm[s], reject |-> TRUE, index |-> msg.index,
                                logTerm |-> 0, entries |-> << >>, commit |-> 0, context |-> ""]
                   IN /\ network' = (network \ {msg}) \cup {resp}
                      /\ UNCHANGED << log, commitIndex >>
               /\ UNCHANGED << state, currentTerm, votedFor, appliedIndex, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

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
            LET resp == [type |-> "MsgHeartbeatResp", from |-> s, to |-> msg.from,
                         term |-> currentTerm[s], context |-> msg.context,
                         logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0, reject |-> FALSE]
            IN /\ state[s] \in {State_Follower, State_Candidate, State_PreCandidate}
               /\ leader' = [leader EXCEPT ![s] = msg.from]
               /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
               /\ IF msg.commit > commitIndex[s] THEN
                   commitIndex' = [commitIndex EXCEPT ![s] = min(msg.commit, LastLogIndex(log[s]))]
                  ELSE
                   commitIndex' = commitIndex
               /\ network' = (network \ {msg}) \cup {resp}
               /\ UNCHANGED << state, currentTerm, votedFor, log, appliedIndex, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

        [] msg.type = "MsgTransferLeader" ->
            IF state[s] = State_Leader THEN
                /\ leadTransferee' = [leadTransferee EXCEPT ![s] = msg.from]
                /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
                /\ network' = network \ {msg}
                /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, voters, learners, pendingConfIndex, kvStore, clientResponses >>
            ELSE
                /\ leader[s] /= None
                /\ LET fwdMsg = [msg EXCEPT !.to = leader[s]]
                IN /\ network' = (network \ {msg}) \cup {fwdMsg}
                   /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

\* Leader sends AppendEntries to a follower
LeaderSendAppend(s, peer) ==
    /\ state[s] = State_Leader
    /\ peer \in voters[s] \ {s}
    /\ LastLogIndex(log[s]) >= nextIndex[s][peer]
    /\ LET prevIndex = nextIndex[s][peer] - 1
           prevTerm = IF prevIndex > 0 THEN (GetLogEntry(log[s], prevIndex)).term ELSE 0
           startSeqIndex = CHOOSE i \in DOMAIN log[s]: log[s][i].index = prevIndex + 1
           entriesToSend = SubSeq(log[s], startSeqIndex, Len(log[s]))
           msg = [type |-> "MsgApp", from |-> s, to |-> peer, term |-> currentTerm[s],
                  logTerm |-> prevTerm, index |-> prevIndex, entries |-> entriesToSend,
                  commit |-> commitIndex[s], reject |-> FALSE, context |-> ""]
    IN /\ network' = network \cup {msg}
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, kvStore, clientResponses >>

\* Leader advances its commit index
LeaderAdvanceCommitIndex(s) ==
    /\ state[s] = State_Leader
    /\ \E n \in (commitIndex[s]+1)..LastLogIndex(log[s]):
        /\ (GetLogEntry(log[s], n)).term = currentTerm[s]
        /\ Cardinality({p \in voters[s] | matchIndex[s][p] >= n}) >= Quorum(voters[s])
    /\ LET newCommitIndex == Max({n \in (commitIndex[s]+1)..LastLogIndex(log[s]) |
                                     (GetLogEntry(log[s], n)).term = currentTerm[s] /\
                                     Cardinality({p \in voters[s] | matchIndex[s][p] >= n}) >= Quorum(voters[s])})
    IN /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
       /\ UNCHANGED << state, currentTerm, votedFor, log, appliedIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, network, kvStore, clientResponses >>

\* A server applies a committed entry to its state machine
Apply(s) ==
    /\ commitIndex[s] > appliedIndex[s]
    /\ LET i == appliedIndex[s] + 1
    /\ LET entry == GetLogEntry(log[s], i)
    IN /\ appliedIndex' = [appliedIndex EXCEPT ![s] = i]
       /\ IF entry.op /= "noop" THEN
           kvStore' = [kvStore EXCEPT ![s][entry.op.key] = entry.op.val]
          ELSE
           kvStore' = kvStore
       /\ UNCHANGED << state, currentTerm, votedFor, log, commitIndex, leader, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, nextIndex, matchIndex, leadTransferee, voters, learners, pendingConfIndex, network, clientResponses >>

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
    \A t \in Nat:
        Cardinality({s \in Servers | state[s] = State_Leader /\ currentTerm[s] = t}) <= 1

\* If two logs contain an entry with the same index and term, they are identical.
LogMatching ==
    \A s1, s2 \in Servers:
        \A i \in 1..min(Len(log[s1]), Len(log[s2])):
            (log[s1][i].term = log[s2][i].term) => (log[s1][i] = log[s2][i])

\* If an entry is committed, it is present in the logs of all leaders of higher terms.
LeaderCompleteness ==
    \A s1 \in Servers:
      \A i \in 1..Len(log[s1]):
        (i <= commitIndex[s1]) =>
            (\A t \in {t_ \in Nat : t_ > log[s1][i].term}:
                \A s2 \in Servers:
                    (state[s2] = State_Leader /\ currentTerm[s2] = t) => (Len(log[s2]) >= i /\ log[s2][i] = log[s1][i]))

\* Entries that are applied must first be committed.
AppliedIsCommitted ==
    \A s \in Servers: appliedIndex[s] <= commitIndex[s]

\* All state machines apply the same sequence of commands.
StateMachineSafety ==
    \A s1, s2 \in Servers:
        \A i \in 1..min(appliedIndex[s1], appliedIndex[s2]):
            GetLogEntry(log[s1], i) = GetLogEntry(log[s2], i)

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

====
