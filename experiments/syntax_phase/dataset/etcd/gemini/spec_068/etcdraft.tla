---- MODULE etcdraft ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    \* @type: Set(Str);
    Servers,
    \* @type: Set(Str);
    ClientValues,
    \* @type: Str;
    DefaultValue,
    \* @type: Int;
    ElectionTimeout,
    \* @type: Int;
    HeartbeatTimeout

ASSUME ElectionTimeout > HeartbeatTimeout
ASSUME HeartbeatTimeout > 0

NilServer == "NilServer"
ServerAndNil == Servers \union {NilServer}

MessageTypes == {
    "MsgHup", "MsgBeat", "MsgProp",
    "MsgApp", "MsgAppResp",
    "MsgVote", "MsgVoteResp",
    "MsgPreVote", "MsgPreVoteResp",
    "MsgSnap", "MsgSnapStatus",
    "MsgHeartbeat", "MsgHeartbeatResp",
    "MsgUnreachable", "MsgTransferLeader",
    "MsgTimeoutNow"
}

ServerStates == {"Follower", "Candidate", "PreCandidate", "Leader"}

CampaignTypes == {"CampaignPreElection", "CampaignElection", "CampaignTransfer"}

\* A log entry contains an index, term, and a value from a client.
\* A special "NoOp" value is used for leader's first entry in a term.
\* A special "ConfChange" value is used for configuration changes.
EntryValue == ClientValues \union {"NoOp", "ConfChange"}

VARIABLES
    \* Raft state variables
    \* @type: [id: Str, val: Str];
    state,
    \* @type: [id: Str, val: Int];
    currentTerm,
    \* @type: [id: Str, val: Str];
    votedFor,
    \* @type: [id: Str, val: <<[index: Int, term: Int, value: Str, config: UNKNOWN]>>];
    log,
    \* @type: [id: Str, val: Int];
    commitIndex,
    \* @type: [id: Str, val: Int];
    appliedIndex,

    \* Leader-specific state
    \* @type: [leader: Str, val: [follower: Str, val: Int]];
    nextIndex,
    \* @type: [leader: Str, val: [follower: Str, val: Int]];
    matchIndex,

    \* Election-related state
    \* @type: [candidate: Str, val: Set(Str)];
    votesGranted,
    \* @type: [candidate: Str, val: Set(Str)];
    preVotesGranted,

    \* Timers
    \* @type: [id: Str, val: Int];
    electionTimer,
    \* @type: [id: Str, val: Int];
    heartbeatTimer,
    \* @type: [id: Str, val: Int];
    randomizedElectionTimeout,

    \* Leader transfer
    \* @type: [id: Str, val: Str];
    leadTransferee,

    \* The network is a set of messages
    \* @type: Set([type: Str, from: Str, to: Str, term: Int, logTerm: Int, index: Int, entries: <<UNKNOWN>>, commit: Int, reject: Bool, context: Str]);
    network,

    \* State machine
    \* @type: [id: Str, val: [key: Str, val: Str]];
    kvStore,

    \* Configuration state
    \* @type: [id: Str, val: [voters: Set(Str), learners: Set(Str)]];
    configs

vars == <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
          nextIndex, matchIndex, votesGranted, preVotesGranted, electionTimer,
          heartbeatTimer, randomizedElectionTimeout, leadTransferee, network, kvStore, configs>>

\* Helper operators
LastLogIndex(s) == IF Len(log[s]) = 0 THEN 0 ELSE log[s][Len(log[s])].index
LastLogTerm(s) == IF Len(log[s]) = 0 THEN 0 ELSE log[s][Len(log[s])].term
GetTerm(lg, idx) == IF idx > 0 /\ idx <= Len(lg) THEN lg[idx].term ELSE 0

Quorum(cfg) == (Cardinality(cfg.voters) \div 2) + 1

IsUpToDate(s, m) ==
    LET lastTerm == LastLogTerm(s)
        lastIndex == LastLogIndex(s)
    IN \/ m.logTerm > lastTerm
       \/ (m.logTerm = lastTerm /\ m.index >= lastIndex)

\* State transition operators
BecomeFollower(s, term, leader) ==
    /\ state' = [state EXCEPT ![s] = "Follower"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = NilServer]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = NilServer]
    /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex,
                   votesGranted, preVotesGranted, heartbeatTimer,
                   randomizedElectionTimeout, network, kvStore, configs>>

BecomePreCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "PreCandidate"]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {s}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex, nextIndex,
                   matchIndex, votesGranted, heartbeatTimer, leadTransferee,
                   randomizedElectionTimeout, network, kvStore, configs>>

BecomeCandidate(s) ==
    /\ state' = [state EXCEPT ![s] = "Candidate"]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = {s}]
    /\ preVotesGranted' = [preVotesGranted EXCEPT ![s] = {}]
    /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex,
                   heartbeatTimer, leadTransferee, randomizedElectionTimeout,
                   network, kvStore, configs>>

BecomeLeader(s) ==
    /\ state' = [state EXCEPT ![s] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [p \in Servers |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [p \in Servers |-> IF p = s THEN LastLogIndex(s) ELSE 0]]
    /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = NilServer]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, appliedIndex,
                   votesGranted, preVotesGranted, electionTimer,
                   randomizedElectionTimeout, network, kvStore, configs>>

\* Initial state
Init ==
    /\ state = [s \in Servers |-> "Follower"]
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> NilServer]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ appliedIndex = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [p \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [p \in Servers |-> 0]]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ preVotesGranted = [s \in Servers |-> {}]
    /\ electionTimer = [s \in Servers |-> 0]
    /\ heartbeatTimer = [s \in Servers |-> 0]
    /\ randomizedElectionTimeout = [s \in Servers |-> ElectionTimeout] \* Simplified
    /\ leadTransferee = [s \in Servers |-> NilServer]
    /\ network = {}
    /\ kvStore = [s \in Servers |-> [v \in ClientValues |-> DefaultValue]]
    /\ configs = [s \in Servers |-> [voters |-> Servers, learners |-> {}]]

\* Actions

\* A client sends a command to a server. If the server is not the leader,
\* it forwards it. For simplicity, we model the client sending to the leader.
ClientRequest(s, val) ==
    /\ state[s] = "Leader"
    /\ leadTransferee[s] = NilServer
    /\ LET newEntry == [index |-> LastLogIndex(s) + 1,
                        term  |-> currentTerm[s],
                        value |-> val,
                        config |-> configs[s]]
           newLog == Append(log[s], newEntry)
    IN /\ log' = [log EXCEPT ![s] = newLog]
       /\ matchIndex' = [matchIndex EXCEPT ![s][s] = newEntry.index]
       /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex,
                      nextIndex, votesGranted, preVotesGranted, electionTimer,
                      heartbeatTimer, randomizedElectionTimeout, leadTransferee,
                      network, kvStore, configs>>

\* A server's election timer times out, causing it to start a (pre)election.
Timeout(s) ==
    /\ state[s] \in {"Follower", "Candidate", "PreCandidate"}
    /\ electionTimer[s] >= randomizedElectionTimeout[s]
    /\ s \in configs[s].voters
    /\ \/ /\ state[s] # "PreCandidate" \* Start PreVote
          /\ BecomePreCandidate(s)
       \/ /\ state[s] = "PreCandidate" \* PreVote failed, try again
          /\ BecomePreCandidate(s)
       \/ /\ state[s] = "Candidate" \* Vote failed, try again
          /\ BecomeCandidate(s)

\* A (pre)candidate sends (pre)vote requests to its peers.
Campaign(s, ctype) ==
    /\ LET
        voters == configs[s].voters
        msgType == IF ctype = "CampaignPreElection" THEN "MsgPreVote" ELSE "MsgVote"
        term == IF ctype = "CampaignPreElection" THEN currentTerm[s] + 1 ELSE currentTerm[s]
        requests == {[
            type    |-> msgType,
            from    |-> s,
            to      |-> p,
            term    |-> term,
            logTerm |-> LastLogTerm(s),
            index   |-> LastLogIndex(s),
            entries |-> << >>,
            commit  |-> 0,
            reject  |-> FALSE,
            context |-> ctype
        ] : p \in voters \ {s}}
    IN /\ network' = network \union requests
       /\ UNCHANGED vars

StartPreVote(s) ==
    /\ state[s] = "PreCandidate"
    /\ Campaign(s, "CampaignPreElection")

StartVote(s) ==
    /\ state[s] = "Candidate"
    /\ Campaign(s, "CampaignTransfer") \* Context can be transfer or election

\* A server receives a vote request.
HandleRequestVote(s, m) ==
    /\ m.type \in {"MsgVote", "MsgPreVote"}
    /\ m.to = s
    /\ LET
        voters == configs[s].voters
        isPreVote == m.type = "MsgPreVote"
        termOK == \/ m.term > currentTerm[s]
                  \/ (m.term = currentTerm[s] /\ state[s] # "Leader" /\
                     (votedFor[s] = NilServer \/ votedFor[s] = m.from))
        logOK == IsUpToDate(s, m)
        grant == termOK /\ logOK
        respType == IF isPreVote THEN "MsgPreVoteResp" ELSE "MsgVoteResp"
        respTerm == IF isPreVote /\ NOT grant THEN currentTerm[s] ELSE m.term
        response == [
            type    |-> respType,
            from    |-> s,
            to      |-> m.from,
            term    |-> respTerm,
            logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0,
            reject  |-> NOT grant,
            context |-> ""
        ]
    IN /\ network' = (network \ {m}) \union {response}
       /\ IF grant /\ NOT isPreVote
          THEN /\ votedFor' = [votedFor EXCEPT ![s] = m.from]
               /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
               /\ state' = [state EXCEPT ![s] = "Follower"]
               /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex,
                              votesGranted, preVotesGranted, electionTimer,
                              heartbeatTimer, randomizedElectionTimeout, leadTransferee,
                              kvStore, configs>>
          ELSE /\ IF m.term > currentTerm[s]
                  THEN /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
                       /\ state' = [state EXCEPT ![s] = "Follower"]
                       /\ votedFor' = [votedFor EXCEPT ![s] = NilServer]
                  ELSE UNCHANGED <<currentTerm, state, votedFor>>
               /\ UNCHANGED <<log, commitIndex, appliedIndex, nextIndex, matchIndex,
                              votesGranted, preVotesGranted, electionTimer,
                              heartbeatTimer, randomizedElectionTimeout, leadTransferee,
                              kvStore, configs>>

\* A candidate receives a vote response.
HandleVoteResponse(s, m) ==
    /\ m.type \in {"MsgVoteResp", "MsgPreVoteResp"}
    /\ m.to = s
    /\ LET isPreVote == m.type = "MsgPreVoteResp"
    IN /\ network' = network \ {m}
       /\ IF m.term > currentTerm[s]
          THEN BecomeFollower(s, m.term, NilServer)
          ELSE IF m.term = currentTerm[s] /\ state[s] = "Candidate" /\ NOT isPreVote
               THEN /\ IF NOT m.reject
                      THEN votesGranted' = [votesGranted EXCEPT ![s] = votesGranted[s] \union {m.from}]
                      ELSE votesGranted' = votesGranted
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                                   nextIndex, matchIndex, preVotesGranted, electionTimer,
                                   heartbeatTimer, randomizedElectionTimeout, leadTransferee,
                                   kvStore, configs>>
               ELSE IF m.term = currentTerm[s] + 1 /\ state[s] = "PreCandidate" /\ isPreVote
                    THEN /\ IF NOT m.reject
                           THEN preVotesGranted' = [preVotesGranted EXCEPT ![s] = preVotesGranted[s] \union {m.from}]
                           ELSE preVotesGranted' = preVotesGranted
                         /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                                        nextIndex, matchIndex, votesGranted, electionTimer,
                                        heartbeatTimer, randomizedElectionTimeout, leadTransferee,
                                        kvStore, configs>>
                    ELSE UNCHANGED <<vars>>

\* A PreCandidate with enough pre-votes becomes a candidate.
PreVoteQuorum(s) ==
    /\ state[s] = "PreCandidate"
    /\ Cardinality(preVotesGranted[s]) >= Quorum(configs[s])
    /\ BecomeCandidate(s)

\* A candidate with enough votes becomes leader.
VoteQuorum(s) ==
    /\ state[s] = "Candidate"
    /\ Cardinality(votesGranted[s]) >= Quorum(configs[s])
    /\ BecomeLeader(s)

\* On becoming leader, append a no-op entry for the new term.
LeaderInitialAppend(s) ==
    /\ state[s] = "Leader"
    /\ (LastLogTerm(s) # currentTerm[s] \/ LastLogIndex(s) = 0)
    /\ LET newEntry == [index |-> LastLogIndex(s) + 1,
                        term  |-> currentTerm[s],
                        value |-> "NoOp",
                        config |-> configs[s]]
           newLog == Append(log[s], newEntry)
    IN /\ log' = [log EXCEPT ![s] = newLog]
       /\ matchIndex' = [matchIndex EXCEPT ![s][s] = newEntry.index]
       /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, appliedIndex,
                      nextIndex, votesGranted, preVotesGranted, electionTimer,
                      heartbeatTimer, randomizedElectionTimeout, leadTransferee,
                      network, kvStore, configs>>

\* Leader sends AppendEntries RPCs to a follower.
LeaderSendAppendEntries(s, p) ==
    /\ state[s] = "Leader"
    /\ p \in Servers \ {s}
    /\ nextIndex[s][p] <= LastLogIndex(s) + 1
    /\ LET prevLogIndex == nextIndex[s][p] - 1
           prevLogTerm == GetTerm(log[s], prevLogIndex)
           entries == SubSeq(log[s], nextIndex[s][p], LastLogIndex(s))
           message == [
                type    |-> "MsgApp",
                from    |-> s,
                to      |-> p,
                term    |-> currentTerm[s],
                logTerm |-> prevLogTerm,
                index   |-> prevLogIndex,
                entries |-> entries,
                commit  |-> commitIndex[s],
                reject  |-> FALSE,
                context |-> ""
           ]
    IN /\ network' = network \union {message}
       /\ nextIndex' = [nextIndex EXCEPT ![s][p] = LastLogIndex(s) + 1]
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                      matchIndex, votesGranted, preVotesGranted, electionTimer,
                      heartbeatTimer, randomizedElectionTimeout, leadTransferee,
                      kvStore, configs>>

\* Leader sends heartbeats (empty AppendEntries) to all followers.
LeaderHeartbeat(s) ==
    /\ state[s] = "Leader"
    /\ heartbeatTimer[s] >= HeartbeatTimeout
    /\ LET messages == {[
            type    |-> "MsgHeartbeat",
            from    |-> s,
            to      |-> p,
            term    |-> currentTerm[s],
            logTerm |-> 0, index |-> 0, entries |-> << >>,
            commit  |-> commitIndex[s],
            reject  |-> FALSE,
            context |-> ""
        ] : p \in configs[s].voters \ {s}}
    IN /\ network' = network \union messages
       /\ heartbeatTimer' = [heartbeatTimer EXCEPT ![s] = 0]
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                      nextIndex, matchIndex, votesGranted, preVotesGranted,
                      electionTimer, randomizedElectionTimeout, leadTransferee,
                      kvStore, configs>>

\* A server receives an AppendEntries or Heartbeat RPC.
HandleAppendEntries(s, m) ==
    /\ m.type \in {"MsgApp", "MsgHeartbeat"}
    /\ m.to = s
    /\ LET
        isHeartbeat == m.type = "MsgHeartbeat"
        response(reject, hintIndex, hintTerm) == [
            type    |-> "MsgAppResp",
            from    |-> s,
            to      |-> m.from,
            term    |-> currentTerm[s],
            logTerm |-> hintTerm,
            index   |-> IF reject THEN m.index ELSE LastLogIndex(s),
            entries |-> << >>,
            commit  |-> 0,
            reject  |-> reject,
            context |-> ""
        ]
    IN /\ network' = network \ {m}
       /\ IF m.term < currentTerm[s]
          THEN /\ network' = (network \ {m}) \union {response(TRUE, 0, 0)}
               /\ UNCHANGED <<vars>>
          ELSE /\ electionTimer' = [electionTimer EXCEPT ![s] = 0]
               /\ currentTerm' = [currentTerm EXCEPT ![s] = m.term]
               /\ state' = [state EXCEPT ![s] = "Follower"]
               /\ IF isHeartbeat
                  THEN /\ commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s], m.commit)]
                       /\ network' = (network \ {m}) \union {[type |-> "MsgHeartbeatResp", from |-> s, to |-> m.from, term |-> currentTerm[s], reject |-> FALSE, logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0, context |-> ""]}
                       /\ UNCHANGED <<votedFor, log, appliedIndex, nextIndex, matchIndex,
                                      votesGranted, preVotesGranted, heartbeatTimer,
                                      randomizedElectionTimeout, leadTransferee, kvStore, configs>>
                  ELSE /\ LET
                            match == \/ m.index = 0
                                     \/ (m.index <= LastLogIndex(s) /\ GetTerm(log[s], m.index) = m.logTerm)
                        IN IF match
                           THEN /\ LET newEntries == m.entries
                                      conflictIndex == CHOOSE i \in 1..Len(newEntries):
                                          m.index + i > LastLogIndex(s) \/ GetTerm(log[s], m.index + i) # newEntries[i].term
                                  IN IF conflictIndex = {}
                                     THEN /\ log' = [log EXCEPT ![s] = log[s] \o newEntries]
                                          /\ commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s], m.commit)]
                                          /\ network' = (network \ {m}) \union {response(FALSE, 0, 0)}
                                     ELSE /\ log' = [log EXCEPT ![s] = SubSeq(log[s], 1, m.index) \o newEntries]
                                          /\ commitIndex' = [commitIndex EXCEPT ![s] = max(commitIndex[s], m.commit)]
                                          /\ network' = (network \ {m}) \union {response(FALSE, 0, 0)}
                               /\ UNCHANGED <<votedFor, appliedIndex, nextIndex, matchIndex,
                                              votesGranted, preVotesGranted, heartbeatTimer,
                                              randomizedElectionTimeout, leadTransferee, kvStore, configs>>
                           ELSE /\ network' = (network \ {m}) \union {response(TRUE, LastLogIndex(s), LastLogTerm(s))}
                                /\ UNCHANGED <<log, commitIndex, votedFor, appliedIndex, nextIndex, matchIndex,
                                               votesGranted, preVotesGranted, heartbeatTimer,
                                               randomizedElectionTimeout, leadTransferee, kvStore, configs>>

\* Leader receives a response to an AppendEntries RPC.
HandleAppendEntriesResponse(s, m) ==
    /\ m.type = "MsgAppResp"
    /\ m.to = s
    /\ state[s] = "Leader"
    /\ network' = network \ {m}
    /\ IF m.term > currentTerm[s]
       THEN BecomeFollower(s, m.term, NilServer)
       ELSE IF m.term = currentTerm[s]
            THEN IF m.reject
                 THEN /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = max(1, m.index)]
                      /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                                     appliedIndex, matchIndex, votesGranted, preVotesGranted,
                                     electionTimer, heartbeatTimer, randomizedElectionTimeout,
                                     leadTransferee, kvStore, configs>>
                 ELSE /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = m.index]
                      /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.index + 1]
                      /\ IF leadTransferee[s] = m.from /\ m.index = LastLogIndex(s)
                         THEN /\ LET msg == [type |-> "MsgTimeoutNow", from |-> s, to |-> m.from, term |-> currentTerm[s], logTerm |-> 0, index |-> 0, entries |-> << >>, commit |-> 0, reject |-> FALSE, context |-> ""]
                              IN network' = (network \ {m}) \union {msg}
                         ELSE UNCHANGED network
                      /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                                     appliedIndex, votesGranted, preVotesGranted,
                                     electionTimer, heartbeatTimer, randomizedElectionTimeout,
                                     leadTransferee, kvStore, configs>>
            ELSE UNCHANGED vars

\* Leader advances its commit index.
LeaderCommit(s) ==
    /\ state[s] = "Leader"
    /\ LET
        voters == configs[s].voters
        PossibleCommits == {i \in (commitIndex[s]+1)..LastLogIndex(s) :
            /\ GetTerm(log[s], i) = currentTerm[s]
            /\ Cardinality({p \in voters : matchIndex[s][p] >= i}) >= Quorum(configs[s])
        }
    IN /\ IF PossibleCommits # {}
          THEN commitIndex' = [commitIndex EXCEPT ![s] = Max(PossibleCommits)]
          ELSE UNCHANGED commitIndex
       /\ UNCHANGED <<state, currentTerm, votedFor, log, appliedIndex,
                      nextIndex, matchIndex, votesGranted, preVotesGranted,
                      electionTimer, heartbeatTimer, randomizedElectionTimeout,
                      leadTransfree, network, kvStore, configs>>

\* Any server applies committed entries to its state machine.
ServerApply(s) ==
    /\ commitIndex[s] > appliedIndex[s]
    /\ LET i == appliedIndex[s] + 1
           entry == log[s][i]
    IN /\ appliedIndex' = [appliedIndex EXCEPT ![s] = i]
       /\ IF entry.value = "ConfChange"
          THEN configs' = [configs EXCEPT ![s] = entry.config]
          ELSE configs' = configs
       /\ kvStore' = [kvStore EXCEPT ![s] = [kvStore[s] EXCEPT ![entry.value] = "some_new_value"]]
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex,
                      nextIndex, matchIndex, votesGranted, preVotesGranted,
                      electionTimer, heartbeatTimer, randomizedElectionTimeout,
                      leadTransferee, network>>

\* Leader transfer
TransferLeader(s, target) ==
    /\ state[s] = "Leader"
    /\ target \in configs[s].voters
    /\ target # s
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = target]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                   nextIndex, matchIndex, votesGranted, preVotesGranted,
                   electionTimer, heartbeatTimer, randomizedElectionTimeout,
                   network, kvStore, configs>>

HandleTimeoutNow(s, m) ==
    /\ m.type = "MsgTimeoutNow"
    /\ m.to = s
    /\ s \in configs[s].voters
    /\ network' = network \ {m}
    /\ IF m.term = currentTerm[s]
       THEN /\ BecomeCandidate(s)
       ELSE UNCHANGED vars

\* Timers advance
Tick ==
    /\ electionTimer' = [s \in Servers |-> IF state[s] # "Leader" THEN electionTimer[s] + 1 ELSE 0]
    /\ heartbeatTimer' = [s \in Servers |-> IF state[s] = "Leader" THEN heartbeatTimer[s] + 1 ELSE 0]
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                   nextIndex, matchIndex, votesGranted, preVotesGranted,
                   randomizedElectionTimeout, leadTransferee, network, kvStore, configs>>

\* Network actions
DropMessage(m) ==
    /\ m \in network
    /\ network' = network \ {m}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, appliedIndex,
                   nextIndex, matchIndex, votesGranted, preVotesGranted,
                   electionTimer, heartbeatTimer, randomizedElectionTimeout,
                   leadTransferee, kvStore, configs>>

\* Next state relation
Next ==
    \/ \E s \in Servers, v \in ClientValues: ClientRequest(s, v)
    \/ \E s \in Servers: Timeout(s)
    \/ \E s \in Servers: StartPreVote(s)
    \/ \E s \in Servers: StartVote(s)
    \/ \E s \in Servers, m \in network: HandleRequestVote(s, m)
    \/ \E s \in Servers, m \in network: HandleVoteResponse(s, m)
    \/ \E s \in Servers: PreVoteQuorum(s)
    \/ \E s \in Servers: VoteQuorum(s)
    \/ \E s \in Servers: LeaderInitialAppend(s)
    \/ \E s \in Servers, p \in Servers: LeaderSendAppendEntries(s, p)
    \/ \E s \in Servers: LeaderHeartbeat(s)
    \/ \E s \in Servers, m \in network: HandleAppendEntries(s, m)
    \/ \E s \in Servers, m \in network: HandleAppendEntriesResponse(s, m)
    \/ \E s \in Servers: LeaderCommit(s)
    \/ \E s \in Servers: ServerApply(s)
    \/ \E s \in Servers, t \in Servers: TransferLeader(s, t)
    \/ \E s \in Servers, m \in network: HandleTimeoutNow(s, m)
    \/ Tick
    \/ \E m \in network: DropMessage(m)

Spec == Init /\ [][Next]_vars

\* Invariants and properties

TypeOK ==
    /\ \A s \in Servers:
        /\ state[s] \in ServerStates
        /\ currentTerm[s] \in Int
        /\ votedFor[s] \in ServerAndNil
        /\ IsSequence(log[s])
        /\ commitIndex[s] \in Int
        /\ appliedIndex[s] \in Int
        /\ electionTimer[s] \in Int
        /\ heartbeatTimer[s] \in Int
        /\ leadTransferee[s] \in ServerAndNil
        /\ configs[s].voters \subseteq Servers
        /\ configs[s].learners \subseteq Servers
    /\ network \subseteq [
        type: MessageTypes, from: ServerAndNil, to: ServerAndNil, term: Int,
        logTerm: Int, index: Int, entries: Seq(Any), commit: Int,
        reject: BOOLEAN, context: STRING
    ]

LeaderSafety ==
    \A t \in {currentTerm[s] : s \in Servers}:
        Cardinality({s \in Servers : state[s] = "Leader" /\ currentTerm[s] = t}) <= 1

TermMonotonicity ==
    \A s \in Servers:
        currentTerm' \in [currentTerm EXCEPT ![s] >= currentTerm[s]]

LogMatching ==
    \A s1, s2 \in Servers:
        \A i \in 1..min(Len(log[s1]), Len(log[s2])):
            (log[s1][i].term = log[s2][i].term) => (log[s1][i] = log[s2][i])

StateMachineSafety ==
    \A s1, s2 \in Servers:
        \A i \in 1..min(Len(log[s1]), Len(log[s2])):
            IF i <= appliedIndex[s1] /\ i <= appliedIndex[s2]
            THEN log[s1][i].value = log[s2][i].value

LeaderCompleteness ==
    \A t \in {currentTerm[s] : s \in Servers}:
        \A s1 \in {s \in Servers : state[s] = "Leader" /\ currentTerm[s] = t}:
            \A i \in 1..commitIndex[s1]:
                \A t2 \in {currentTerm[s] : s \in Servers}:
                    IF t2 > t THEN
                        \A s2 \in {s \in Servers : state[s] = "Leader" /\ currentTerm[s] = t2}:
                            i <= LastLogIndex(s2) /\ log[s2][i].term = log[s1][i].term

CommitIndexIsSane ==
    \A s \in Servers:
        /\ commitIndex[s] <= LastLogIndex(s)
        /\ appliedIndex[s] <= commitIndex[s]

====
