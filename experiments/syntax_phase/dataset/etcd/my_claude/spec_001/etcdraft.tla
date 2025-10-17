---- MODULE etcdraft ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Servers, MaxTerm, MaxLogLen

VARIABLES 
    currentTerm,
    votedFor,
    log,
    state,
    commitIndex,
    nextIndex,
    matchIndex,
    votes,
    preVotes,
    electionTimeout,
    heartbeatTimeout,
    messages,
    leaderId

vars == <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, messages, leaderId>>

States == {"Follower", "PreCandidate", "Candidate", "Leader"}

MessageTypes == {"MsgHup", "MsgVote", "MsgVoteResp", "MsgPreVote", "MsgPreVoteResp", "MsgApp", "MsgAppResp", "MsgHeartbeat", "MsgHeartbeatResp", "MsgProp"}

Message == [type: MessageTypes, from: Servers, to: Servers, term: Nat, logTerm: Nat, index: Nat, entries: Seq(Nat), commit: Nat, reject: BOOLEAN]

Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> "None"]
    /\ log = [s \in Servers |-> <<>>]
    /\ state = [s \in Servers |-> "Follower"]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ nextIndex = [s \in Servers |-> [t \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [t \in Servers |-> 0]]
    /\ votes = [s \in Servers |-> {}]
    /\ preVotes = [s \in Servers |-> {}]
    /\ electionTimeout = [s \in Servers |-> TRUE]
    /\ heartbeatTimeout = [s \in Servers |-> FALSE]
    /\ messages = {}
    /\ leaderId = [s \in Servers |-> "None"]

Send(m) == messages' = messages \cup {m}

Reply(response, request) ==
    Send([type |-> response.type, from |-> response.from, to |-> response.to, 
          term |-> response.term, logTerm |-> response.logTerm, index |-> response.index,
          entries |-> response.entries, commit |-> response.commit, reject |-> response.reject])

Discard(m) == messages' = messages \ {m}

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LogOk(i, j) ==
    /\ Len(log[i]) >= j
    /\ j > 0 => log[i][j] = currentTerm[i]

IsUpToDate(i, j) ==
    \/ LastTerm(log[i]) > LastTerm(log[j])
    \/ /\ LastTerm(log[i]) = LastTerm(log[j])
       /\ Len(log[i]) >= Len(log[j])

CanVote(i, j, logTerm, logIndex) ==
    /\ currentTerm[i] < currentTerm[j] \/ votedFor[i] \in {"None", j}
    /\ \/ logTerm > LastTerm(log[i])
       \/ /\ logTerm = LastTerm(log[i])
          /\ logIndex >= Len(log[i])

BecomeFollower(i, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ state' = [state EXCEPT ![i] = "Follower"]
    /\ votedFor' = [votedFor EXCEPT ![i] = "None"]
    /\ leaderId' = [leaderId EXCEPT ![i] = "None"]
    /\ votes' = [votes EXCEPT ![i] = {}]
    /\ preVotes' = [preVotes EXCEPT ![i] = {}]

BecomePreCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = "PreCandidate"]
    /\ preVotes' = [preVotes EXCEPT ![i] = {i}]
    /\ leaderId' = [leaderId EXCEPT ![i] = "None"]

BecomeCandidate(i) ==
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ state' = [state EXCEPT ![i] = "Candidate"]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votes' = [votes EXCEPT ![i] = {i}]
    /\ leaderId' = [leaderId EXCEPT ![i] = "None"]

BecomeLeader(i) ==
    /\ state' = [state EXCEPT ![i] = "Leader"]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ leaderId' = [leaderId EXCEPT ![i] = i]

ElectionTimeout(i) ==
    /\ state[i] \in {"Follower", "PreCandidate", "Candidate"}
    /\ electionTimeout[i] = TRUE
    /\ IF state[i] = "Follower"
       THEN /\ BecomePreCandidate(i)
            /\ \A j \in Servers \ {i} :
                Send([type |-> "MsgPreVote", from |-> i, to |-> j, term |-> currentTerm[i] + 1,
                      logTerm |-> LastTerm(log[i]), index |-> Len(log[i]),
                      entries |-> <<>>, commit |-> 0, reject |-> FALSE])
       ELSE IF state[i] = "PreCandidate"
            THEN /\ BecomeCandidate(i)
                 /\ \A j \in Servers \ {i} :
                     Send([type |-> "MsgVote", from |-> i, to |-> j, term |-> currentTerm[i],
                           logTerm |-> LastTerm(log[i]), index |-> Len(log[i]),
                           entries |-> <<>>, commit |-> 0, reject |-> FALSE])
            ELSE /\ BecomeCandidate(i)
                 /\ \A j \in Servers \ {i} :
                     Send([type |-> "MsgVote", from |-> i, to |-> j, term |-> currentTerm[i],
                           logTerm |-> LastTerm(log[i]), index |-> Len(log[i]),
                           entries |-> <<>>, commit |-> 0, reject |-> FALSE])
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<log, commitIndex, matchIndex, heartbeatTimeout, messages>>

HeartbeatTimeout(i) ==
    /\ state[i] = "Leader"
    /\ heartbeatTimeout[i] = TRUE
    /\ \A j \in Servers \ {i} :
        Send([type |-> "MsgHeartbeat", from |-> i, to |-> j, term |-> currentTerm[i],
              logTerm |-> 0, index |-> 0, entries |-> <<>>, 
              commit |-> commitIndex[i], reject |-> FALSE])
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, leaderId>>

HandleMsgPreVote(i, j, m) ==
    /\ m.type = "MsgPreVote"
    /\ m.to = i
    /\ m.from = j
    /\ IF /\ m.term > currentTerm[i]
          /\ CanVote(i, j, m.logTerm, m.index)
       THEN /\ Reply([type |-> "MsgPreVoteResp", from |-> i, to |-> j, term |-> m.term,
                      logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> FALSE], m)
            /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, leaderId>>
       ELSE /\ Reply([type |-> "MsgPreVoteResp", from |-> i, to |-> j, term |-> currentTerm[i],
                      logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> TRUE], m)
            /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, leaderId>>
    /\ Discard(m)

HandleMsgPreVoteResp(i, j, m) ==
    /\ m.type = "MsgPreVoteResp"
    /\ m.to = i
    /\ m.from = j
    /\ state[i] = "PreCandidate"
    /\ IF /\ m.term = currentTerm[i] + 1
          /\ ~m.reject
       THEN /\ preVotes' = [preVotes EXCEPT ![i] = preVotes[i] \cup {j}]
            /\ IF Cardinality(preVotes'[i]) * 2 > Cardinality(Servers)
               THEN /\ BecomeCandidate(i)
                    /\ \A k \in Servers \ {i} :
                        Send([type |-> "MsgVote", from |-> i, to |-> k, term |-> currentTerm'[i],
                              logTerm |-> LastTerm(log[i]), index |-> Len(log[i]),
                              entries |-> <<>>, commit |-> 0, reject |-> FALSE])
               ELSE UNCHANGED <<currentTerm, state, votedFor, votes, leaderId>>
            /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, electionTimeout, heartbeatTimeout>>
       ELSE UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, leaderId>>
    /\ Discard(m)

HandleMsgVote(i, j, m) ==
    /\ m.type = "MsgVote"
    /\ m.to = i
    /\ m.from = j
    /\ IF m.term > currentTerm[i]
       THEN BecomeFollower(i, m.term)
       ELSE UNCHANGED <<currentTerm, state, votedFor, votes, preVotes, leaderId>>
    /\ IF /\ m.term >= currentTerm'[i]
          /\ CanVote(i, j, m.logTerm, m.index)
       THEN /\ votedFor' = [votedFor' EXCEPT ![i] = j]
            /\ Reply([type |-> "MsgVoteResp", from |-> i, to |-> j, term |-> m.term,
                      logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> FALSE], m)
       ELSE Reply([type |-> "MsgVoteResp", from |-> i, to |-> j, term |-> currentTerm'[i],
                   logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> TRUE], m)
    /\ Discard(m)
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, electionTimeout, heartbeatTimeout>>

HandleMsgVoteResp(i, j, m) ==
    /\ m.type = "MsgVoteResp"
    /\ m.to = i
    /\ m.from = j
    /\ state[i] = "Candidate"
    /\ IF /\ m.term = currentTerm[i]
          /\ ~m.reject
       THEN /\ votes' = [votes EXCEPT ![i] = votes[i] \cup {j}]
            /\ IF Cardinality(votes'[i]) * 2 > Cardinality(Servers)
               THEN BecomeLeader(i)
               ELSE UNCHANGED <<currentTerm, state, votedFor, nextIndex, matchIndex, leaderId>>
            /\ UNCHANGED <<log, commitIndex, preVotes, electionTimeout, heartbeatTimeout>>
       ELSE IF m.term > currentTerm[i]
            THEN BecomeFollower(i, m.term)
            ELSE UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, leaderId>>
    /\ Discard(m)

HandleMsgApp(i, j, m) ==
    /\ m.type = "MsgApp"
    /\ m.to = i
    /\ m.from = j
    /\ IF m.term > currentTerm[i]
       THEN BecomeFollower(i, m.term)
       ELSE UNCHANGED <<currentTerm, state, votedFor, votes, preVotes, leaderId>>
    /\ IF m.term >= currentTerm'[i]
       THEN /\ leaderId' = [leaderId' EXCEPT ![i] = j]
            /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
            /\ IF /\ m.index <= Len(log[i])
                  /\ (m.index = 0 \/ log[i][m.index] = m.logTerm)
               THEN /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, m.index) \o m.entries]
                    /\ commitIndex' = [commitIndex EXCEPT ![i] = m.commit]
                    /\ Reply([type |-> "MsgAppResp", from |-> i, to |-> j, term |-> currentTerm'[i],
                              logTerm |-> 0, index |-> Len(log'[i]), entries |-> <<>>, commit |-> 0, reject |-> FALSE], m)
               ELSE Reply([type |-> "MsgAppResp", from |-> i, to |-> j, term |-> currentTerm'[i],
                           logTerm |-> 0, index |-> m.index, entries |-> <<>>, commit |-> 0, reject |-> TRUE], m)
       ELSE /\ Reply([type |-> "MsgAppResp", from |-> i, to |-> j, term |-> currentTerm'[i],
                      logTerm |-> 0, index |-> m.index, entries |-> <<>>, commit |-> 0, reject |-> TRUE], m)
            /\ UNCHANGED <<log, commitIndex, electionTimeout>>
    /\ Discard(m)
    /\ UNCHANGED <<nextIndex, matchIndex, heartbeatTimeout>>

HandleMsgAppResp(i, j, m) ==
    /\ m.type = "MsgAppResp"
    /\ m.to = i
    /\ m.from = j
    /\ state[i] = "Leader"
    /\ IF m.term > currentTerm[i]
       THEN BecomeFollower(i, m.term)
       ELSE IF /\ m.term = currentTerm[i]
               /\ ~m.reject
            THEN /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.index + 1]
                 /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.index]
                 /\ UNCHANGED <<currentTerm, state, votedFor, votes, preVotes, leaderId>>
            ELSE IF /\ m.term = currentTerm[i]
                    /\ m.reject
                 THEN /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max(1, nextIndex[i][j] - 1)]
                      /\ UNCHANGED <<currentTerm, state, votedFor, matchIndex, votes, preVotes, leaderId>>
                 ELSE UNCHANGED <<currentTerm, state, votedFor, nextIndex, matchIndex, votes, preVotes, leaderId>>
    /\ Discard(m)
    /\ UNCHANGED <<log, commitIndex, electionTimeout, heartbeatTimeout>>

HandleMsgHeartbeat(i, j, m) ==
    /\ m.type = "MsgHeartbeat"
    /\ m.to = i
    /\ m.from = j
    /\ IF m.term > currentTerm[i]
       THEN BecomeFollower(i, m.term)
       ELSE UNCHANGED <<currentTerm, state, votedFor, votes, preVotes, leaderId>>
    /\ IF m.term >= currentTerm'[i]
       THEN /\ leaderId' = [leaderId' EXCEPT ![i] = j]
            /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
            /\ commitIndex' = [commitIndex EXCEPT ![i] = m.commit]
       ELSE UNCHANGED <<electionTimeout, commitIndex>>
    /\ Reply([type |-> "MsgHeartbeatResp", from |-> i, to |-> j, term |-> currentTerm'[i],
              logTerm |-> 0, index |-> 0, entries |-> <<>>, commit |-> 0, reject |-> FALSE], m)
    /\ Discard(m)
    /\ UNCHANGED <<log, nextIndex, matchIndex, heartbeatTimeout>>

HandleMsgHeartbeatResp(i, j, m) ==
    /\ m.type = "MsgHeartbeatResp"
    /\ m.to = i
    /\ m.from = j
    /\ state[i] = "Leader"
    /\ IF m.term > currentTerm[i]
       THEN BecomeFollower(i, m.term)
       ELSE UNCHANGED <<currentTerm, state, votedFor, votes, preVotes, leaderId>>
    /\ Discard(m)
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, electionTimeout, heartbeatTimeout>>

ClientRequest(i, v) ==
    /\ state[i] = "Leader"
    /\ Len(log[i]) < MaxLogLen
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, messages, leaderId>>

AppendEntries(i, j) ==
    /\ state[i] = "Leader"
    /\ j \in Servers \ {i}
    /\ nextIndex[i][j] <= Len(log[i])
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex = 0 THEN 0 ELSE log[i][prevLogIndex]
           entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
       IN Send([type |-> "MsgApp", from |-> i, to |-> j, term |-> currentTerm[i],
                logTerm |-> prevLogTerm, index |-> prevLogIndex, entries |-> entries,
                commit |-> commitIndex[i], reject |-> FALSE])
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, leaderId>>

AdvanceCommitIndex(i) ==
    /\ state[i] = "Leader"
    /\ \E index \in (commitIndex[i] + 1)..Len(log[i]) :
        /\ log[i][index] = currentTerm[i]
        /\ Cardinality({j \in Servers : matchIndex[i][j] >= index}) * 2 > Cardinality(Servers)
        /\ commitIndex' = [commitIndex EXCEPT ![i] = index]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, nextIndex, matchIndex, votes, preVotes, electionTimeout, heartbeatTimeout, messages, leaderId>>

TimeoutElapsed(i) ==
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, preVotes, heartbeatTimeout, messages, leaderId>>

HeartbeatElapsed(i) ==
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, preVotes, electionTimeout, messages, leaderId>>

ReceiveMessage(m) ==
    /\ m \in messages
    /\ \/ HandleMsgPreVote(m.to, m.from, m)
       \/ HandleMsgPreVoteResp(m.to, m.from, m)
       \/ HandleMsgVote(m.to, m.from, m)
       \/ HandleMsgVoteResp(m.to, m.from, m)
       \/ HandleMsgApp(m.to, m.from, m)
       \/ HandleMsgAppResp(m.to, m.from, m)
       \/ HandleMsgHeartbeat(m.to, m.from, m)
       \/ HandleMsgHeartbeatResp(m.to, m.from, m)

Next ==
    \/ \E i \in Servers : ElectionTimeout(i)
    \/ \E i \in Servers : HeartbeatTimeout(i)
    \/ \E i \in Servers : TimeoutElapsed(i)
    \/ \E i \in Servers : HeartbeatElapsed(i)
    \/ \E i \in Servers, v \in 1..MaxTerm : ClientRequest(i, v)
    \/ \E i, j \in Servers : AppendEntries(i, j)
    \/ \E i \in Servers : AdvanceCommitIndex(i)
    \/ \E m \in messages : ReceiveMessage(m)

Spec == Init /\ [][Next]_vars

====