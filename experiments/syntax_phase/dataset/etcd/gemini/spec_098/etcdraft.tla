---- MODULE etcdraft ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS
    \* @type: Set(Str);
    Servers,
    \* @type: Set(Str);
    Clients,
    \* @type: Set(<<Str, Str, Str>>);
    ClientValues

VARIABLES
    \* Global state
    \* @type: Set(<<type: Str, from: Str, to: Str, term: Int, logTerm: Int, index: Int, entries: Seq(<<term: Int, value: <<Str, Str, Str>>>>), commit: Int, reject: Bool, rejectHint: Int, context: Str>>);
    network,
    \* @type: Str -> Str;
    kvStore,

    \* Per-server state
    \* @type: Str -> Str;
    state,
    \* @type: Str -> Int;
    currentTerm,
    \* @type: Str -> Str;
    votedFor,
    \* @type: Str -> Seq(<<term: Int, value: <<Str, Str, Str>>, type: Str>>);
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
    \* @type: Str -> Set(<<req: <<type: Str, from: Str, to: Str, term: Int, logTerm: Int, index: Int, entries: Seq(<<term: Int, value: <<Str, Str, Str>>>>), commit: Int, reject: Bool, rejectHint: Int, context: Str>>, acks: Set(Str)>>);
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
Quorum(s) == {i \in s: Cardinality(s) < 2 * Cardinality({j \in s : matchIndex[i][j] >= commitIndex[i]})}
IsUpToDate(logA, logB) ==
    LET lastTermA == IF Len(logA) > 0 THEN logA[Len(logA)].term ELSE 0 END
        lastIndexA == Len(logA)
        lastTermB == IF Len(logB) > 0 THEN logB[Len(logB)].term ELSE 0 END
        lastIndexB == Len(logB)
    IN (lastTermA > lastTermB) \/ (lastTermA = lastTermB /\ lastIndexA >= lastIndexB)

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
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> 0] WITH [s] = LastLogIndex(s)]
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
           ELSE CASE msg.type = MsgApp          -> HandleAppendEntries(s, msg)
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
                     existingEntries == SubSeq(log[s], 1, prevLogIndex)
                     conflictingIndex == CHOOSE i \in DOMAIN newEntries:
                                            /\ firstNewIndex + i - 1 <= LastLogIndex(s)
                                            /\ log[s][firstNewIndex + i - 1].term # newEntries[i].term
                     finalLog == IF conflictingIndex = {}
                                 THEN existingEntries \o newEntries
                                 ELSE SubSeq(log[s], 1, firstNewIndex + conflictingIndex - 2) \o SubSeq(newEntries, conflictingIndex, Len(newEntries))
                IN /\ log' = [log EXCEPT ![s] = finalLog]
                   /\ commitIndex' = [commitIndex EXCEPT ![s] = Min({msg.commit, LastLogIndex(s)})]
                   /\ LET resp == [
                            type |-> MsgAppResp, from |-> s, to |-> msg.from, term |-> currentTerm[s],
                            logTerm |-> 0, index |-> LastLogIndex(s), entries |-> <<>>,
                            commit |-> 0, reject |-> FALSE, rejectHint |-> 0, context |-> ""
                        ]
                   IN network' = (network \ {msg}) \cup {resp}
          ELSE /\ LET rejectHint == Min({LastLogIndex(s), prevLogIndex})
                     resp == [
                        type |-> MsgAppResp, from |-> s, to |-> msg.from, term |-> currentTerm[s],
                        logTerm |-> IF rejectHint > 0 THEN log[s][rejectHint].term ELSE 0,
                        index |-> msg.index, entries |-> <<>>, commit |-> 0,
                        reject |-> TRUE, rejectHint |-> rejectHint, context |-> ""
                     ]
                 IN network' = (network \ {msg}) \cup {resp}
    /\ UNCHANGED <<kvStore, appliedIndex, nextIndex, matchIndex>>

HandleAppendEntriesResp(s, msg) ==
    /\ state[s] = StateLeader
    /\ LET peer == msg.from
    IN /\ IF msg.reject
          THEN /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![peer] = msg.rejectHint + 1]]
               /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![peer] = msg.rejectHint]]
               /\ UNCHANGED <<log, commitIndex>>
          ELSE /\ nextIndex' = [nextIndex EXCEPT ![s] = [nextIndex[s] EXCEPT ![peer] = msg.index + 1]]
               /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![peer] = msg.index]]
               /\ LET newCommitIndex ==
                        CHOOSE c \in (commitIndex[s]+1)..LastLogIndex(s):
                            /\ log[s][c].term = currentTerm[s]
                            /\ Cardinality({p \in Servers | matchIndex[s][p] >= c}) * 2 > Cardinality(Servers)
                  IN IF newCommitIndex # {}
                     THEN commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
                     ELSE UNCHANGED commitIndex
    /\ IF leaderTransferTarget[s] = peer /\ matchIndex'[s][peer] = LastLogIndex(s)
       THEN LET timeoutMsg == [
                type |-> MsgTimeoutNow, from |-> s, to |-> peer, term |-> currentTerm[s],
                logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                reject |-> FALSE, rejectHint |-> 0, context |-> ""
            ]
            IN network' = (network \ {msg}) \cup {timeoutMsg}
       ELSE network' = network \ {msg}
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
               IN network' = (network \ {msg}) \cup {resp}
          ELSE /\ LET resp == [
                        type |-> respType, from |-> s, to |-> cand, term |-> currentTerm[s],
                        logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0,
                        reject |-> TRUE, rejectHint |-> 0, context |-> ""
                    ]
               IN network' = (network \ {msg}) \cup {resp}
               /\ UNCHANGED votedFor
    /\ UNCHANGED <<state, currentTerm, log, commitIndex, appliedIndex, electionTimer, randomizedElectionTimeout, nextIndex, matchIndex, leader, leaderTransferTarget, votesGranted, preVotesGranted, lastAck, readOnlyState, kvStore>>

HandleRequestVoteResp(s, msg) ==
    /\ LET voter == msg.from
    IN /\ IF msg.type = MsgPreVoteResp
          THEN /\ state[s] = StatePreCandidate
               /\ IF NOT msg.reject
                  THEN /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = preVotesGranted[s] \cup {voter}]
                       /\ IF Cardinality(preVotesGranted'[s]) * 2 > Cardinality(Servers)
                          THEN BecomeCandidate(s)
                          ELSE UNCHANGED <<state, currentTerm, votedFor, votesGranted>>
                  ELSE UNCHANGED <<state, currentTerm, votedFor, votesGranted, preVotesGranted>>
          ELSE /\ state[s] = StateCandidate
               /\ IF NOT msg.reject
                  THEN /\ votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \cup {voter}]
                       /\ IF Cardinality(votesGranted'[s]) * 2 > Cardinality(Servers)
                          THEN BecomeLeader(s)
                          ELSE UNCHANGED <<state, leader, nextIndex, matchIndex, log>>
                  ELSE UNCHANGED <<state, leader, nextIndex, matchIndex, log, votesGranted>>
    /\ network' = network \ {msg}
    /\ UNCHANGED <<kvStore, commitIndex, appliedIndex, electionTimer, randomizedElectionTimeout, leaderTransferTarget, lastAck, readOnlyState>>

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
    IN network' = (network \ {msg}) \cup {resp}
    /\ UNCHANGED <<log, kvStore, appliedIndex, nextIndex, matchIndex>>

HandleHeartbeatResp(s, msg) ==
    /\ state[s] = StateLeader
    /\ lastAck' = [lastAck EXCEPT ![s] = lastAck[s] \cup {msg.from}]
    /\ LET newReadOnlyState == {
            rs \in readOnlyState[s] |
            [
                req |-> rs.req,
                acks |-> IF rs.req.context = msg.context THEN rs.acks \cup {msg.from} ELSE rs.acks
            ]
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
       /\ network' = (network \ {msg}) \cup newMsgs
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex, electionTimer, randomizedElectionTimeout, nextIndex, matchIndex, leader, leaderTransferTarget, votesGranted, preVotesGranted, kvStore>>

HandleProp(s, msg) ==
    /\ IF state[s] = StateLeader
       THEN /\ IF leaderTransferTarget[s] # ""
              THEN network' = network \ {msg} /\ UNCHANGED <<vars \ {network}>>
              ELSE /\ LET newEntry == [term |-> currentTerm[s], value |-> msg.entries[1].value, type |-> EntryNormal]
                         newLog == Append(log[s], newEntry)
                     IN /\ log' = [log EXCEPT ![s] = newLog]
                        /\ matchIndex' = [matchIndex EXCEPT ![s] = [matchIndex[s] EXCEPT ![s] = Len(newLog)]]
                        /\ LET newMsgs == {
                                [
                                    type |-> MsgApp, from |-> s, to |-> peer, term |-> currentTerm[s],
                                    logTerm |-> log[s][nextIndex[s][peer]-1].term, index |-> nextIndex[s][peer]-1,
                                    entries |-> SubSeq(newLog, nextIndex[s][peer], Len(newLog)),
                                    commit |-> commitIndex[s], reject |-> FALSE, rejectHint |-> 0, context |-> ""
                                ] : peer \in Servers \ {s}
                            }
                        IN network' = (network \ {msg}) \cup newMsgs
                        /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex, electionTimer, randomizedElectionTimeout, nextIndex, leader, leaderTransferTarget, votesGranted, preVotesGranted, lastAck, readOnlyState, kvStore>>
       ELSE IF leader # ""
       THEN /\ LET fwdMsg == [msg EXCEPT !.to = leader]
            IN network' = (network \ {msg}) \cup {fwdMsg}
            /\ UNCHANGED <<vars \ {network}>>
       ELSE /\ network' = network \ {msg}
            /\ UNCHANGED <<vars \ {network}>>

HandleTransferLeader(s, msg) ==
    /\ IF state[s] = StateLeader
       THEN /\ leaderTransferTarget' = [leaderTransferTarget EXCEPT ![s] = msg.from]
            /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
            /\ network' = network \ {msg}
            /\ UNCHANGED <<vars \ {leaderTransferTarget, electionTimer, network}>>
       ELSE IF leader # ""
       THEN /\ LET fwdMsg == [msg EXCEPT !.to = leader]
            IN network' = (network \ {msg}) \cup {fwdMsg}
            /\ UNCHANGED <<vars \ {network}>>
       ELSE /\ network' = network \ {msg}
            /\ UNCHANGED <<vars \ {network}>>

HandleTimeoutNow(s, msg) ==
    /\ state[s] \in {StateFollower, StateCandidate}
    /\ leaderTransferTarget' = [leaderTransferTarget EXCEPT ![s] = s]
    /\ BecomeCandidate(s)
    /\ network' = network \ {msg}
    /\ UNCHANGED <<kvStore, log, commitIndex, appliedIndex, nextIndex, matchIndex, leader, votesGranted, preVotesGranted, lastAck, readOnlyState>>

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
               IN network' = (network \ {msg}) \cup newMsgs
       ELSE IF leader # ""
       THEN /\ LET fwdMsg == [msg EXCEPT !.to = leader]
            IN network' = (network \ {msg}) \cup {fwdMsg}
       ELSE network' = network \ {msg}
    /\ UNCHANGED <<vars \ {network, readOnlyState}>>

HandleReadIndexResp(s, msg) ==
    /\ state[s] = StateFollower
    /\ network' = network \ {msg}
    /\ UNCHANGED <<vars \ {network}>>

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
        entries: Seq([term: Int, value: [op: STRING, key: STRING, val: STRING]]),
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

LeaderCompleteness ==
    \A t \in 1..MaxSet(currentTerm):
        LET committedInTerm(t) == {e \in UNION {log[s] : s \in Servers} |
                                    \E s \in Servers:
                                        /\ e.term = t
                                        /\ e.index <= commitIndex[s]}
            leadersInTerm(t) == {s \in Servers | state[s] = StateLeader /\ currentTerm[s] = t}
        IN \A e \in committedInTerm(t):
            \A l \in leadersInTerm(t):
                e \in log[l]

LogMatchingProperty ==
    \A s1, s2 \in Servers:
        \A i \in 1..Min({Len(log[s1]), Len(log[s2])}):
            (log[s1][i].term = log[s2][i].term) => (log[s1][i] = log[s2][i])

LeaderLogsOnlyAppend ==
    \A s \in Servers:
        (state[s] = StateLeader) => (log[s] = Head(log'[s], Len(log[s])))

StateConsistency ==
    \A t \in 1..MaxSet(currentTerm):
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