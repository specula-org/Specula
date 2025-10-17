---- MODULE etcdraft ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    \* @type: Set(Str);
    Servers,
    \* @type: Set(Str);
    Clients,
    \* @type: Set([op: Str, key: Str, val: Str]);
    ClientValues,
    STRING

VARIABLES
    \* Global state
    \* @type: Set([type: Str, from: Str, to: Str, term: Int, logTerm: Int, index: Int, entries: Seq([term: Int, value: [op: Str, key: Str, val: Str]]), commit: Int, reject: Bool, rejectHint: Int, context: Str]);
    network,
    \* @type: Str -> [key: Str -> Str];
    kvStore,

    \* Per-server state
    \* @type: Str -> Str;
    state,
    \* @type: Str -> Int;
    currentTerm,
    \* @type: Str -> Str;
    votedFor,
    \* @type: Str -> Seq([term: Int, value: [op: Str, key: Str, val: Str], type: Str]);
    log,
    \* @type: Str -> Int;
    commitIndex,
    \* @type: Str -> Int;
    appliedIndex,
    \* @type: Str -> Int;
    electionTimer,
    \* @type: Str -> Int;
    randomizedElectionTimeout,

    \* Leader-specific state
    \* @type: Str -> (Str -> Int);
    nextIndex,
    \* @type: Str -> (Str -> Int);
    matchIndex,
    \* @type: Str -> Str;
    leader,
    \* @type: Str -> Str;
    leaderTransferTarget,
    \* @type: Str -> Set(Str);
    votesGranted,
    \* @type: Str -> Set(Str);
    lastAck,
    \* @type: Str -> Set([req: [type: Str, from: Str, to: Str, term: Int, logTerm: Int, index: Int, entries: Seq([term: Int, value: [op: Str, key: Str, val: Str]]), commit: Int, reject: Bool, rejectHint: Int, context: Str], acks: Set(Str)]);
    readOnlyState,

    \* PreVote-specific state
    \* @type: Str -> Set(Str);
    preVotesGranted

\* Configuration constants
ElectionTimeoutMin == 5
ElectionTimeoutMax == 10
HeartbeatInterval == 2
PreVoteEnabled == TRUE
CheckQuorumEnabled == TRUE

\* Message types
MsgProp         == "MsgProp"
MsgApp          == "MsgApp"
MsgAppResp      == "MsgAppResp"
MsgVote         == "MsgVote"
MsgVoteResp     == "MsgVoteResp"
MsgSnap         == "MsgSnap"
MsgHeartbeat    == "MsgHeartbeat"
MsgHeartbeatResp== "MsgHeartbeatResp"
MsgHup          == "MsgHup"
MsgBeat         == "MsgBeat"
MsgCheckQuorum  == "MsgCheckQuorum"
MsgPreVote      == "MsgPreVote"
MsgPreVoteResp  == "MsgPreVoteResp"
MsgTransferLeader == "MsgTransferLeader"
MsgTimeoutNow   == "MsgTimeoutNow"
MsgReadIndex    == "MsgReadIndex"
MsgReadIndexResp== "MsgReadIndexResp"

\* Server states
StateFollower     == "StateFollower"
StateCandidate    == "StateCandidate"
StatePreCandidate == "StatePreCandidate"
StateLeader       == "StateLeader"

\* Log entry types
EntryNormal     == "EntryNormal"
EntryConfChange == "EntryConfChange"

\* Helper functions
IsUpToDate(infoA, infoB) ==
    (infoA.term > infoB.term) \/ (infoA.term = infoB.term /\ infoA.index >= infoB.index)

LastLogIndex(s) == Len(log[s])
LastLogTerm(s) == IF LastLogIndex(s) > 0 THEN log[s][LastLogIndex(s)].term ELSE 0

vars == <<network, kvStore, state, currentTerm, votedFor, log, commitIndex, appliedIndex,
          electionTimer, randomizedElectionTimeout, nextIndex, matchIndex, leader,
          leaderTransferTarget, votesGranted, lastAck, readOnlyState, preVotesGranted>>

Init ==
    /\ network = {}
    /\ kvStore = [s \in Servers |-> [key \in {} |-> ""]]
    /\ state = [s \in Servers |-> StateFollower]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> ""]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ appliedIndex = [s \in Servers |-> 0]
    /\ electionTimer = [s \in Servers |-> 0]
    /\ randomizedElectionTimeout = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ leader = ""
    /\ leaderTransferTarget = [s \in Servers |-> ""]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ preVotesGranted = [s \in Servers |-> {}]
    /\ lastAck = [s \in Servers |-> {}]
    /\ readOnlyState = [s \in Servers |-> {}]

\* Actions

BecomeFollower(s, term, newLeader) ==
    /\ state' = [state EXCEPT ![s] = StateFollower]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = ""]
    /\ leader' = IF newLeader # "" THEN newLeader ELSE leader
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ leaderTransferTarget' = [leaderTransferTarget EXCEPT ![s] = ""]
    /\ randomizedElectionTimeout' = [randomizedElectionTimeout EXCEPT ![s] = CHOOSE t \in ElectionTimeoutMin..ElectionTimeoutMax: TRUE]
    /\ UNCHANGED <<network, kvStore, log, commitIndex, appliedIndex, nextIndex, matchIndex, votesGranted, preVotesGranted, lastAck, readOnlyState>>

StartElection(s, campaignType) ==
    LET nextTerm == IF campaignType = MsgPreVote THEN currentTerm[s] + 1 ELSE currentTerm'[s]
        voteMsgType == IF campaignType = MsgPreVote THEN MsgPreVote ELSE MsgVote
        voteRespMsgType == IF campaignType = MsgPreVote THEN MsgPreVoteResp ELSE MsgVoteResp
        voters == Servers
        newMsgs == {
            [
                type |-> voteMsgType, from |-> s, to |-> peer, term |-> nextTerm,
                logTerm |-> LastLogTerm(s), index |-> LastLogIndex(s),
                entries |-> <<>>, commit |-> 0, reject |-> FALSE, rejectHint |-> 0,
                context |-> IF leaderTransferTarget[s] # "" THEN "transfer" ELSE ""
            ] : peer \in voters \ {s}
        } \union {
            [
                type |-> voteRespMsgType, from |-> s, to |-> s, term |-> nextTerm,
                logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                reject |-> FALSE, rejectHint |-> 0, context |-> ""
            ]
        }
    IN
    /\ network' = network \cup newMsgs
    /\ UNCHANGED <<kvStore, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader, leaderTransferTarget, lastAck, readOnlyState>>

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = StatePreCandidate]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ StartElection(s, MsgPreVote)
    /\ UNCHANGED <<currentTerm, votedFor, leader, randomizedElectionTimeout>>

BecomeCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = StateCandidate]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ StartElection(s, MsgVote)
    /\ UNCHANGED <<leader, randomizedElectionTimeout>>

BecomeLeader(s) ==
    /\ state' = [state EXCEPT ![s] = StateLeader]
    /\ leader' = s
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> IF p = s THEN LastLogIndex(s) ELSE 0]]
    /\ leaderTransferTarget' = [leaderTransferTarget EXCEPT ![s] = ""]
    /\ lastAck' = [lastAck EXCEPT ![s] = {s}]
    /\ readOnlyState' = [readOnlyState EXCEPT ![s] = {}]
    /\ LET newEntry == [term |-> currentTerm[s], value |-> [op |-> "nop", key |-> "", val |-> ""], type |-> EntryNormal]
    IN /\ log' = [log EXCEPT ![s] = Append(log[s], newEntry)]
       /\ network' = network \cup {
            [
                type |-> MsgApp, from |-> s, to |-> peer, term |-> currentTerm[s],
                logTerm |-> LastLogTerm(s), index |-> LastLogIndex(s),
                entries |-> <<newEntry>>, commit |-> commitIndex[s],
                reject |-> FALSE, rejectHint |-> 0, context |-> ""
            ] : peer \in Servers \ {s}
        }
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, appliedIndex, electionTimer, randomizedElectionTimeout, votesGranted, preVotesGranted, kvStore>>

Timeout(s) ==
    /\ electionTimer[s] >= randomizedElectionTimeout[s]
    /\ state[s] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ IF PreVoteEnabled
       THEN BecomePreCandidate(s)
       ELSE BecomeCandidate(s)
    /\ UNCHANGED <<network, kvStore, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader, leaderTransferTarget, votesGranted, lastAck, readOnlyState>>

LeaderHeartbeat(s) ==
    /\ state[s] = StateLeader
    /\ electionTimer[s] % HeartbeatInterval = 0
    /\ LET newMsgs == {
            [
                type |-> MsgHeartbeat, from |-> s, to |-> peer, term |-> currentTerm[s],
                logTerm |-> 0, index |-> 0, entries |-> <<>>,
                commit |-> Min({commitIndex[s], matchIndex[s][peer]}),
                reject |-> FALSE, rejectHint |-> 0, context |-> ""
            ] : peer \in Servers \ {s}
        }
    IN /\ network' = network \cup newMsgs
       /\ UNCHANGED <<vars \ {network}>>

CheckQuorum(s) ==
    /\ CheckQuorumEnabled
    /\ state[s] = StateLeader
    /\ electionTimer[s] > 0
    /\ electionTimer[s] % randomizedElectionTimeout[s] = 0
    /\ LET activePeers == {p \in Servers | p \in lastAck[s]}
    IN /\ IF Cardinality(activePeers) * 2 > Cardinality(Servers)
          THEN /\ lastAck' = [lastAck EXCEPT ![s] = {s}]
               /\ UNCHANGED <<vars \ {lastAck}>>
          ELSE /\ BecomeFollower(s, currentTerm[s], "")
               /\ UNCHANGED <<kvStore, log, commitIndex, appliedIndex, nextIndex, matchIndex, votesGranted, preVotesGranted, lastAck>>

Tick(s) ==
    /\ electionTimer' = [electionTimer EXCEPT ![s] = electionTimer[s] + 1]
    /\ UNCHANGED <<vars \ {electionTimer}>>

ClientRequest(client, s, val) ==
    /\ val \in ClientValues
    /\ LET msg == [
            type |-> MsgProp, from |-> client, to |-> s, term |-> 0,
            logTerm |-> 0, index |-> 0, entries |-> <<[term |-> 0, value |-> val, type |-> EntryNormal]>>,
            commit |-> 0, reject |-> FALSE, rejectHint |-> 0, context |-> ""
        ]
    IN /\ network' = network \cup {msg}
       /\ UNCHANGED <<vars \ {network}>>

HandleReceive(s) ==
    \E msg \in network:
        /\ msg.to = s
        /\ LET from == msg.from
               term == msg.term
        IN
        /\ IF term > currentTerm[s]
           THEN /\ \/ /\ msg.type \in {MsgApp, MsgHeartbeat, MsgSnap}
                      /\ BecomeFollower(s, term, from)
                \/ /\ msg.type \in {MsgVote, MsgVoteResp}
                      /\ BecomeFollower(s, term, "")
                \/ /\ msg.type \in {MsgPreVote, MsgPreVoteResp} /\ term > currentTerm[s]
                      /\ UNCHANGED <<vars>>
           ELSE IF term < currentTerm[s]
           THEN /\ network' = network \ {msg}
                /\ UNCHANGED <<vars \ {network}>>
           ELSE /\ network' = network \ {msg}
                /\ CASE msg.type = MsgApp          -> HandleAppendEntries(s, msg)
                 [] msg.type = MsgAppResp      -> HandleAppendEntriesResp(s, msg)
                 [] msg.type = MsgVote         -> HandleRequestVote(s, msg)
                 [] msg.type = MsgVoteResp     -> HandleRequestVoteResp(s, msg)
                 [] msg.type = MsgHeartbeat    -> HandleHeartbeat(s, msg)
                 [] msg.type = MsgHeartbeatResp-> HandleHeartbeatResp(s, msg)
                 [] msg.type = MsgProp         -> HandleProp(s, msg)
                 [] msg.type = MsgPreVote      -> HandleRequestVote(s, msg)
                 [] msg.type = MsgPreVoteResp  -> HandleRequestVoteResp(s, msg)
                 [] msg.type = MsgTransferLeader -> HandleTransferLeader(s, msg)
                 [] msg.type = MsgTimeoutNow   -> HandleTimeoutNow(s, msg)
                 [] msg.type = MsgReadIndex    -> HandleReadIndex(s, msg)
                 [] msg.type = MsgReadIndexResp-> HandleReadIndexResp(s, msg)
                 [] OTHER -> UNCHANGED <<vars>>

HandleAppendEntries(s, msg) ==
    /\ state[s] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ IF state[s] # StateFollower
       THEN BecomeFollower(s, msg.term, msg.from)
       ELSE /\ leader' = msg.from
            /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
            /\ UNCHANGED <<state, currentTerm, votedFor, randomizedElectionTimeout, leaderTransferTarget, votesGranted, preVotesGranted, lastAck, readOnlyState>>
    /\ LET prevLogIndex == msg.index
           prevLogTerm == msg.logTerm
           logOk == /\ prevLogIndex = 0
                    \/ /\ prevLogIndex <= LastLogIndex(s)
                       /\ log[s][prevLogIndex].term = prevLogTerm
    IN /\ IF logOk
          THEN /\ LET newEntries == msg.entries
                     firstNewIndex == prevLogIndex + 1
                     conflictingSet == { i \in DOMAIN newEntries:
                                            /\ firstNewIndex + i - 1 <= LastLogIndex(s)
                                            /\ log[s][firstNewIndex + i - 1].term # newEntries[i].term }
                     finalLog == IF conflictingSet = {}
                                 THEN SubSeq(log[s], 1, prevLogIndex) \o newEntries
                                 ELSE LET conflictingIndex == Min(conflictingSet)
                                      IN SubSeq(log[s], 1, firstNewIndex + conflictingIndex - 2) \o SubSeq(newEntries, conflictingIndex, Len(newEntries))
                IN /\ log' = [log EXCEPT ![s] = finalLog]
                   /\ commitIndex' = [commitIndex EXCEPT ![s] = Min({msg.commit, Len(finalLog)})]
                   /\ LET resp == [
                            type |-> MsgAppResp, from |-> s, to |-> msg.from, term |-> currentTerm[s],
                            logTerm |-> 0, index |-> Len(finalLog), entries |-> <<>>,
                            commit |-> 0, reject |-> FALSE, rejectHint |-> 0, context |-> ""
                        ]
                   IN network' = network' \cup {resp}
          ELSE /\ LET rejectHint == Min({LastLogIndex(s), prevLogIndex})
                     resp == [
                        type |-> MsgAppResp, from |-> s, to |-> msg.from, term |-> currentTerm[s],
                        logTerm |-> IF rejectHint > 0 THEN log[s][rejectHint].term ELSE 0,
                        index |-> msg.index, entries |-> <<>>, commit |-> 0,
                        reject |-> TRUE, rejectHint |-> rejectHint, context |-> ""
                     ]
                 IN network' = network' \cup {resp}
    /\ UNCHANGED <<kvStore, appliedIndex, nextIndex, matchIndex>>

HandleAppendEntriesResp(s, msg) ==
    /\ state[s] = StateLeader
    /\ LET peer == msg.from
    IN /\ IF msg.reject
          THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![peer] = msg.rejectHint + 1]]
               /\ UNCHANGED <<log, commitIndex, matchIndex>>
          ELSE /\ LET newMatchIndexVal == msg.index
                   newMatchIndexMap == [matchIndex[s] EXCEPT ![peer] = newMatchIndexVal]
               IN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![peer] = newMatchIndexVal + 1]]
                  /\ matchIndex' = [matchIndex EXCEPT ![s] = newMatchIndexMap]
                  /\ LET possibleCommits ==
                           { c \in (commitIndex[s]+1)..LastLogIndex(s):
                               /\ log[s][c].term = currentTerm[s]
                               /\ Cardinality({p \in Servers | newMatchIndexMap[p] >= c}) * 2 > Cardinality(Servers) }
                     IN IF possibleCommits # {}
                        THEN commitIndex' = [commitIndex EXCEPT ![s] = Max(possibleCommits)]
                        ELSE UNCHANGED commitIndex
                  /\ IF leaderTransferTarget[s] = peer /\ newMatchIndexVal = LastLogIndex(s)
                     THEN LET timeoutMsg == [
                              type |-> MsgTimeoutNow, from |-> s, to |-> peer, term |-> currentTerm[s],
                              logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                              reject |-> FALSE, rejectHint |-> 0, context |-> ""
                          ]
                          IN network' = network' \cup {timeoutMsg}
                     ELSE TRUE
    /\ UNCHANGED <<state, currentTerm, votedFor, kvStore, appliedIndex, electionTimer, randomizedElectionTimeout, leader, leaderTransferTarget, votesGranted, preVotesGranted, lastAck, readOnlyState>>

HandleRequestVote(s, msg) ==
    /\ LET cand == msg.from
           candTerm == msg.term
           candLogTerm == msg.logTerm
           candLogIndex == msg.index
           voteGranted == \/ votedFor[s] = ""
                          \/ votedFor[s] = cand
           logOK == IsUpToDate([term |-> candLogTerm, index |-> candLogIndex], [term |-> LastLogTerm(s), index |-> LastLogIndex(s)])
           inLease == leader # "" /\ electionTimer[s] < randomizedElectionTimeout[s]
           forceVote == msg.context = "transfer"
           canVote == (voteGranted /\ logOK) /\ (forceVote \/ NOT inLease)
           respType == IF msg.type = MsgPreVote THEN MsgPreVoteResp ELSE MsgVoteResp
    IN /\ IF canVote
          THEN /\ IF msg.type = MsgVote THEN votedFor' = [votedFor EXCEPT ![s] = cand] ELSE UNCHANGED votedFor
               /\ LET resp == [
                        type |-> respType, from |-> s, to |-> cand, term |-> currentTerm[s],
                        logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                        reject |-> FALSE, rejectHint |-> 0, context |-> ""
                    ]
               IN network' = network' \cup {resp}
          ELSE /\ LET resp == [
                        type |-> respType, from |-> s, to |-> cand, term |-> currentTerm[s],
                        logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                        reject |-> TRUE, rejectHint |-> 0, context |-> ""
                    ]
               IN network' = network' \cup {resp}
               /\ UNCHANGED votedFor
    /\ UNCHANGED <<state, currentTerm, log, commitIndex, appliedIndex, electionTimer, randomizedElectionTimeout, nextIndex, matchIndex, leader, leaderTransferTarget, votesGranted, preVotesGranted, lastAck, readOnlyState, kvStore>>

HandleRequestVoteResp(s, msg) ==
    /\ LET voter == msg.from
    IN /\ IF msg.type = MsgPreVoteResp
          THEN /\ state[s] = StatePreCandidate
               /\ IF NOT msg.reject
                  THEN /\ LET newPreVotes == preVotesGranted[s] \cup {voter}
                       IN /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = newPreVotes]
                          /\ IF Cardinality(newPreVotes) * 2 > Cardinality(Servers)
                             THEN BecomeCandidate(s)
                             ELSE UNCHANGED <<state, currentTerm, votedFor, votesGranted>>
                  ELSE UNCHANGED <<state, currentTerm, votedFor, votesGranted, preVotesGranted>>
          ELSE /\ state[s] = StateCandidate
               /\ IF NOT msg.reject
                  THEN /\ LET newVotes == votesGranted[s] \cup {voter}
                       IN /\ votesGranted' = [votesGranted EXCEPT ![s] = newVotes]
                          /\ IF Cardinality(newVotes) * 2 > Cardinality(Servers)
                             THEN BecomeLeader(s)
                             ELSE UNCHANGED <<state, leader, nextIndex, matchIndex, log>>
                  ELSE UNCHANGED <<state, leader, nextIndex, matchIndex, log, votesGranted>>
    /\ UNCHANGED <<kvStore, commitIndex, appliedIndex, electionTimer, randomizedElectionTimeout>>

HandleHeartbeat(s, msg) ==
    /\ state[s] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ IF state[s] # StateFollower
       THEN BecomeFollower(s, msg.term, msg.from)
       ELSE /\ leader' = msg.from
            /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
            /\ UNCHANGED <<state, currentTerm, votedFor, randomizedElectionTimeout, leaderTransferTarget, votesGranted, preVotesGranted, lastAck, readOnlyState>>
    /\ commitIndex' = [commitIndex EXCEPT ![s] = Min({msg.commit, LastLogIndex(s)})]
    /\ LET resp == [
            type |-> MsgHeartbeatResp, from |-> s, to |-> msg.from, term |-> currentTerm[s],
            logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
            reject |-> FALSE, rejectHint |-> 0, context |-> msg.context
        ]
    IN network' = network' \cup {resp}
    /\ UNCHANGED <<log, kvStore, appliedIndex, nextIndex, matchIndex>>

HandleHeartbeatResp(s, msg) ==
    /\ state[s] = StateLeader
    /\ lastAck' = [lastAck EXCEPT ![s] = lastAck[s] \cup {msg.from}]
    /\ LET newReadOnlyState == {
            [
                req |-> rs.req,
                acks |-> IF rs.req.context = msg.context THEN rs.acks \cup {msg.from} ELSE rs.acks
            ] : rs \in readOnlyState[s]
        }
        readyToRespond == { rs \in newReadOnlyState | Cardinality(rs.acks) * 2 > Cardinality(Servers) }
        newMsgs == {
            [
                type |-> MsgReadIndexResp, from |-> s, to |-> rs.req.from, term |-> currentTerm[s],
                logTerm |-> 0, index |-> rs.req.index, entries |-> rs.req.entries,
                commit |-> 0, reject |-> FALSE, rejectHint |-> 0, context |-> ""
            ] : rs \in readyToRespond
        }
    IN /\ readOnlyState' = [readOnlyState EXCEPT ![s] = newReadOnlyState \ readyToRespond]
       /\ network' = network' \cup newMsgs
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, electionTimer, randomizedElectionTimeout, nextIndex, matchIndex, leader, leaderTransferTarget, votesGranted, preVotesGranted, kvStore>>

HandleProp(s, msg) ==
    /\ IF state[s] = StateLeader
       THEN /\ IF leaderTransferTarget[s] # ""
              THEN UNCHANGED <<vars>>
              ELSE /\ LET newEntry == [term |-> currentTerm[s], value |-> msg.entries[1].value, type |-> EntryNormal]
                         newLog == Append(log[s], newEntry)
                     IN /\ log' = [log EXCEPT ![s] = newLog]
                        /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![s] = Len(newLog)]]
                        /\ LET newMsgs == {
                                [
                                    type |-> MsgApp, from |-> s, to |-> peer, term |-> currentTerm[s],
                                    logTerm |-> LET prevIdx = nextIndex[s][peer]-1 IN IF prevIdx > 0 THEN log[s][prevIdx].term ELSE 0,
                                    index |-> nextIndex[s][peer]-1,
                                    entries |-> SubSeq(newLog, nextIndex[s][peer], Len(newLog)),
                                    commit |-> commitIndex[s], reject |-> FALSE, rejectHint |-> 0, context |-> ""
                                ] : peer \in Servers \ {s}
                            }
                        IN network' = network' \cup newMsgs
                        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex, electionTimer, randomizedElectionTimeout, nextIndex, leader, leaderTransferTarget, votesGranted, preVotesGranted, lastAck, readOnlyState, kvStore>>
       ELSE IF leader # ""
       THEN /\ LET fwdMsg == [msg EXCEPT !.to = leader]
            IN network' = network' \cup {fwdMsg}
            /\ UNCHANGED <<vars \ {network}>>
       ELSE UNCHANGED <<vars>>

HandleTransferLeader(s, msg) ==
    /\ IF state[s] = StateLeader
       THEN /\ leaderTransferTarget' = [leaderTransferTarget EXCEPT ![s] = msg.from]
            /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
            /\ UNCHANGED <<vars \ {leaderTransferTarget, electionTimer}>>
       ELSE IF leader # ""
       THEN /\ LET fwdMsg == [msg EXCEPT !.to = leader]
            IN network' = network' \cup {fwdMsg}
            /\ UNCHANGED <<vars \ {network}>>
       ELSE UNCHANGED <<vars>>

HandleTimeoutNow(s, msg) ==
    /\ state[s] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ LET nextTerm == currentTerm[s] + 1
          voters == Servers
          newMsgs == {
              [
                  type |-> MsgVote, from |-> s, to |-> peer, term |-> nextTerm,
                  logTerm |-> LastLogTerm(s), index |-> LastLogIndex(s),
                  entries |-> <<>>, commit |-> 0, reject |-> FALSE, rejectHint |-> 0,
                  context |-> "transfer"
              ] : peer \in voters \ {s}
          } \union {
              [
                  type |-> MsgVoteResp, from |-> s, to |-> s, term |-> nextTerm,
                  logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                  reject |-> FALSE, rejectHint |-> 0, context |-> ""
              ]
          }
    IN /\ state' = [state EXCEPT ![s] = StateCandidate]
       /\ currentTerm' = [currentTerm EXCEPT ![s] = nextTerm]
       /\ votedFor' = [votedFor EXCEPT ![s] = s]
       /\ votesGranted' = [votesGranted EXCEPT ![s] = {}]
       /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {}]
       /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
       /\ network' = network' \cup newMsgs
       /\ UNCHANGED <<kvStore, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader,
                     leaderTransferTarget, randomizedElectionTimeout, lastAck, readOnlyState>>

HandleReadIndex(s, msg) ==
    /\ IF state[s] = StateLeader
       THEN /\ LET readReq == [req |-> msg, acks |-> {s}]
            IN /\ readOnlyState' = [readOnlyState EXCEPT ![s] = readOnlyState[s] \cup {readReq}]
               /\ LET heartbeatCtx == msg.entries[1].value.val
                      newMsgs == {
                        [
                            type |-> MsgHeartbeat, from |-> s, to |-> peer, term |-> currentTerm[s],
                            logTerm |-> 0, index |-> 0, entries |-> <<>>,
                            commit |-> Min({commitIndex[s], matchIndex[s][peer]}),
                            reject |-> FALSE, rejectHint |-> 0, context |-> heartbeatCtx
                        ] : peer \in Servers \ {s}
                      }
               IN network' = network' \cup newMsgs
               /\ UNCHANGED <<vars \ {network, readOnlyState}>>
       ELSE IF leader # ""
       THEN /\ LET fwdMsg == [msg EXCEPT !.to = leader]
            IN network' = network' \cup {fwdMsg}
            /\ UNCHANGED <<vars \ {network}>>
       ELSE UNCHANGED <<vars>>

HandleReadIndexResp(s, msg) ==
    /\ state[s] = StateFollower
    /\ UNCHANGED <<vars>>

ApplyLogEntries(s) ==
    /\ commitIndex[s] > appliedIndex[s]
    /\ LET i == appliedIndex[s] + 1
           entry == log[s][i]
    IN /\ appliedIndex' = [appliedIndex EXCEPT ![s] = i]
       /\ IF entry.type = EntryNormal
          THEN /\ LET op == entry.value.op
                     key == entry.value.key
                     val == entry.value.val
                 IN kvStore' = [kvStore EXCEPT ![s] =
                                    CASE op = "put" -> [kvStore[s] EXCEPT ![key] = val]
                                    [] op = "del" -> [k \in DOMAIN kvStore[s] \ {key} |-> kvStore[s][k]]
                                    [] OTHER -> kvStore[s]]
          ELSE UNCHANGED kvStore
    /\ UNCHANGED <<network, state, currentTerm, votedFor, log, commitIndex, electionTimer, randomizedElectionTimeout, nextIndex, matchIndex, leader, leaderTransferTarget, votesGranted, preVotesGranted, lastAck, readOnlyState>>

Next ==
    \/ \E s \in Servers: Timeout(s)
    \/ \E s \in Servers: LeaderHeartbeat(s)
    \/ \E s \in Servers: CheckQuorum(s)
    \/ \E s \in Servers: Tick(s)
    \/ \E c \in Clients, s \in Servers, v \in ClientValues: ClientRequest(c, s, v)
    \/ \E s \in Servers: HandleReceive(s)
    \/ \E s \in Servers: ApplyLogEntries(s)
    \/ \E msg \in network: network' = network \ {msg} /\ UNCHANGED <<vars \ {network}>>

Spec == Init /\ [][Next]_vars

\* Invariants and Properties

TypeOK ==
    /\ network \subseteq [
        type: STRING, from: STRING, to: STRING, term: Int, logTerm: Int, index: Int,
        entries: Seq([term: Int, value: [op: STRING, key: STRING, val: STRING], type: STRING]),
        commit: Int, reject: BOOLEAN, rejectHint: Int, context: STRING
    ]
    /\ \A s \in Servers:
        /\ state[s] \in {StateFollower, StateCandidate, StatePreCandidate, StateLeader}
        /\ currentTerm[s] \in Int
        /\ votedFor[s] \in Servers \cup {""}
        /\ log[s] \in Seq([term: Int, value: [op: STRING, key: STRING, val: STRING], type: STRING])
        /\ commitIndex[s] \in Nat
        /\ appliedIndex[s] \in Nat
        /\ appliedIndex[s] <= commitIndex[s]
        /\ commitIndex[s] <= Len(log[s])

LogMatchingProperty ==
    \A s1, s2 \in Servers:
        \A i \in 1..Min({Len(log[s1]), Len(log[s2])}):
            (log[s1][i].term = log[s2][i].term) => (log[s1][i] = log[s2][i])

LeaderLogsOnlyAppend ==
    \A s \in Servers:
        (state[s] = StateLeader) => (log[s] = Head(log'[s], Len(log[s])))

StateConsistency ==
    \A t \in {currentTerm[s] : s \in Servers}:
        Cardinality({s \in Servers | state[s] = StateLeader /\ currentTerm[s] = t}) <= 1

AppliedLogsAreSame ==
    \A s1, s2 \in Servers:
        LET len1 = appliedIndex[s1]
            len2 = appliedIndex[s2]
        IN \A i \in 1..Min({len1, len2}):
            log[s1][i] = log[s2][i]

Linearizability == \A s1, s2 \in Servers: kvStore[s1] = kvStore[s2]

EventuallyLeaderElected == <>(\E s \in Servers: state[s] = StateLeader)
EventuallyApplied == \A s \in Servers, i \in 1..Len(log[s]):
    (i <= commitIndex[s]) ~> (i <= appliedIndex[s])

====
