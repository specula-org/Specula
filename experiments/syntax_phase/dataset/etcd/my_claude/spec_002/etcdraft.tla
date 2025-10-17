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
    messages,
    electionTimeout,
    heartbeatTimeout

vars == <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, messages, electionTimeout, heartbeatTimeout>>

None == 0
StateFollower == "Follower"
StateCandidate == "Candidate" 
StateLeader == "Leader"
StatePreCandidate == "PreCandidate"

MsgHup == "MsgHup"
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgHeartbeat == "MsgHeartbeat"
MsgHeartbeatResp == "MsgHeartbeatResp"
MsgProp == "MsgProp"

Message(mtype, mfrom, mto, mterm, mlogTerm, mindex, mentries, mcommit, mvoteGranted, mreject) ==
    [type |-> mtype, from |-> mfrom, to |-> mto, term |-> mterm, 
     logTerm |-> mlogTerm, index |-> mindex, entries |-> mentries,
     commit |-> mcommit, voteGranted |-> mvoteGranted, reject |-> mreject]

Entry(eterm, eindex, edata) == [term |-> eterm, index |-> eindex, data |-> edata]

Init ==
    /\ currentTerm = [i \in Servers |-> 1]
    /\ votedFor = [i \in Servers |-> None]
    /\ log = [i \in Servers |-> <<>>]
    /\ state = [i \in Servers |-> StateFollower]
    /\ commitIndex = [i \in Servers |-> 0]
    /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ votes = [i \in Servers |-> {}]
    /\ messages = {}
    /\ electionTimeout = [i \in Servers |-> FALSE]
    /\ heartbeatTimeout = [i \in Servers |-> FALSE]

Send(m) == messages' = messages \cup {m}

Reply(response, request) ==
    Send([type |-> response.type, from |-> response.from, to |-> response.to,
          term |-> response.term, logTerm |-> response.logTerm, index |-> response.index,
          entries |-> response.entries, commit |-> response.commit, 
          voteGranted |-> response.voteGranted, reject |-> response.reject])

Discard(m) == messages' = messages \ {m}

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term
LastIndex(xlog) == Len(xlog)

IsUpToDate(i, j) ==
    \/ LastTerm(log[i]) > LastTerm(log[j])
    \/ /\ LastTerm(log[i]) = LastTerm(log[j])
       /\ LastIndex(log[i]) >= LastIndex(log[j])

CanVote(i, j, logTerm, logIndex) ==
    /\ IsUpToDate(j, i)
    /\ \/ votedFor[i] = None
       \/ votedFor[i] = j

BecomeFollower(i, term) ==
    /\ currentTerm' = [currentTerm EXCEPT ![i] = term]
    /\ state' = [state EXCEPT ![i] = StateFollower]
    /\ votedFor' = [votedFor EXCEPT ![i] = None]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votes>>

BecomePreCandidate(i) ==
    /\ state' = [state EXCEPT ![i] = StatePreCandidate]
    /\ votes' = [votes EXCEPT ![i] = {}]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, nextIndex, matchIndex>>

BecomeCandidate(i) ==
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ state' = [state EXCEPT ![i] = StateCandidate]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votes' = [votes EXCEPT ![i] = {i}]
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

BecomeLeader(i) ==
    /\ state' = [state EXCEPT ![i] = StateLeader]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> LastIndex(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votes>>

ElectionTimeout(i) ==
    /\ electionTimeout[i] = TRUE
    /\ state[i] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ BecomePreCandidate(i)
    /\ LET preVoteMsg == Message(MsgPreVote, i, j, currentTerm[i] + 1, 
                                LastTerm(log[i]), LastIndex(log[i]), <<>>, 0, FALSE, FALSE)
       IN /\ Send(preVoteMsg)
          /\ \A j \in Servers \ {i} : Send([preVoteMsg EXCEPT !.to = j])
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<heartbeatTimeout>>

Campaign(i) ==
    /\ state[i] = StatePreCandidate
    /\ Cardinality(votes[i]) * 2 > Cardinality(Servers)
    /\ BecomeCandidate(i)
    /\ LET voteMsg == Message(MsgVote, i, j, currentTerm'[i], 
                             LastTerm(log[i]), LastIndex(log[i]), <<>>, 0, FALSE, FALSE)
       IN /\ Send(voteMsg)
          /\ \A j \in Servers \ {i} : Send([voteMsg EXCEPT !.to = j])
    /\ UNCHANGED <<electionTimeout, heartbeatTimeout>>

HandlePreVote(i, j, m) ==
    /\ m.type = MsgPreVote
    /\ m.to = i
    /\ m.from = j
    /\ IF /\ m.term > currentTerm[i]
          /\ CanVote(i, j, m.logTerm, m.index)
       THEN /\ Reply(Message(MsgPreVoteResp, i, j, m.term, 0, 0, <<>>, 0, TRUE, FALSE), m)
            /\ UNCHANGED vars
       ELSE /\ Reply(Message(MsgPreVoteResp, i, j, currentTerm[i], 0, 0, <<>>, 0, FALSE, TRUE), m)
            /\ UNCHANGED vars

HandlePreVoteResponse(i, j, m) ==
    /\ m.type = MsgPreVoteResp
    /\ m.to = i
    /\ m.from = j
    /\ state[i] = StatePreCandidate
    /\ IF m.voteGranted
       THEN /\ votes' = [votes EXCEPT ![i] = votes[i] \cup {j}]
            /\ IF Cardinality(votes'[i]) * 2 > Cardinality(Servers)
               THEN Campaign(i)
               ELSE UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex>>
       ELSE UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes>>

HandleVote(i, j, m) ==
    /\ m.type = MsgVote
    /\ m.to = i
    /\ m.from = j
    /\ IF /\ m.term >= currentTerm[i]
          /\ CanVote(i, j, m.logTerm, m.index)
       THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
            /\ votedFor' = [votedFor EXCEPT ![i] = j]
            /\ state' = [state EXCEPT ![i] = StateFollower]
            /\ Reply(Message(MsgVoteResp, i, j, m.term, 0, 0, <<>>, 0, TRUE, FALSE), m)
            /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votes>>
       ELSE /\ Reply(Message(MsgVoteResp, i, j, currentTerm[i], 0, 0, <<>>, 0, FALSE, TRUE), m)
            /\ UNCHANGED vars

HandleVoteResponse(i, j, m) ==
    /\ m.type = MsgVoteResp
    /\ m.to = i
    /\ m.from = j
    /\ state[i] = StateCandidate
    /\ m.term = currentTerm[i]
    /\ IF m.voteGranted
       THEN /\ votes' = [votes EXCEPT ![i] = votes[i] \cup {j}]
            /\ IF Cardinality(votes'[i]) * 2 > Cardinality(Servers)
               THEN BecomeLeader(i)
               ELSE UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex>>
       ELSE UNCHANGED vars

ClientRequest(i, data) ==
    /\ state[i] = StateLeader
    /\ Len(log[i]) < MaxLogLen
    /\ LET entry == Entry(currentTerm[i], LastIndex(log[i]) + 1, data)
       IN log' = [log EXCEPT ![i] = Append(log[i], entry)]
    /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex, nextIndex, matchIndex, votes, messages, electionTimeout, heartbeatTimeout>>

SendAppendEntries(i, j) ==
    /\ state[i] = StateLeader
    /\ i # j
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[i])
                         THEN log[i][prevLogIndex].term
                         ELSE 0
           entries == IF nextIndex[i][j] <= Len(log[i])
                     THEN SubSeq(log[i], nextIndex[i][j], Len(log[i]))
                     ELSE <<>>
       IN Send(Message(MsgApp, i, j, currentTerm[i], prevLogTerm, prevLogIndex, 
                      entries, commitIndex[i], FALSE, FALSE))
    /\ UNCHANGED vars

HandleAppendEntries(i, j, m) ==
    /\ m.type = MsgApp
    /\ m.to = i
    /\ m.from = j
    /\ IF m.term < currentTerm[i]
       THEN /\ Reply(Message(MsgAppResp, i, j, currentTerm[i], 0, m.index, <<>>, 0, FALSE, TRUE), m)
            /\ UNCHANGED vars
       ELSE /\ IF m.term > currentTerm[i]
               THEN BecomeFollower(i, m.term)
               ELSE UNCHANGED <<currentTerm, votedFor, state, nextIndex, matchIndex, votes>>
            /\ LET logOk == \/ m.index = 0
                           \/ /\ m.index > 0
                              /\ m.index <= Len(log[i])
                              /\ log[i][m.index].term = m.logTerm
               IN IF logOk
                  THEN /\ log' = [log EXCEPT ![i] = 
                                   SubSeq(log[i], 1, m.index) \o m.entries]
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = 
                                          IF m.commit > commitIndex[i]
                                          THEN Min(m.commit, Len(log'[i]))
                                          ELSE commitIndex[i]]
                       /\ Reply(Message(MsgAppResp, i, j, currentTerm'[i], 0, 
                                       m.index + Len(m.entries), <<>>, 0, FALSE, FALSE), m)
                  ELSE /\ Reply(Message(MsgAppResp, i, j, currentTerm'[i], 0, 
                                       m.index, <<>>, 0, FALSE, TRUE), m)
                       /\ UNCHANGED <<log, commitIndex>>

HandleAppendEntriesResponse(i, j, m) ==
    /\ m.type = MsgAppResp
    /\ m.to = i
    /\ m.from = j
    /\ state[i] = StateLeader
    /\ m.term = currentTerm[i]
    /\ IF m.reject
       THEN /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max(1, nextIndex[i][j] - 1)]
            /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, matchIndex, votes>>
       ELSE /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.index + 1]
            /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.index]
            /\ LET N == m.index
                   agreeCount == Cardinality({k \in Servers : matchIndex'[i][k] >= N})
               IN IF /\ N > commitIndex[i]
                     /\ agreeCount * 2 > Cardinality(Servers)
                     /\ N <= Len(log[i])
                     /\ log[i][N].term = currentTerm[i]
                  THEN commitIndex' = [commitIndex EXCEPT ![i] = N]
                  ELSE UNCHANGED commitIndex
            /\ UNCHANGED <<currentTerm, votedFor, log, state, votes>>

SendHeartbeat(i) ==
    /\ state[i] = StateLeader
    /\ heartbeatTimeout[i] = TRUE
    /\ \A j \in Servers \ {i} :
         Send(Message(MsgHeartbeat, i, j, currentTerm[i], 0, 0, <<>>, commitIndex[i], FALSE, FALSE))
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout>>

HandleHeartbeat(i, j, m) ==
    /\ m.type = MsgHeartbeat
    /\ m.to = i
    /\ m.from = j
    /\ IF m.term >= currentTerm[i]
       THEN /\ BecomeFollower(i, m.term)
            /\ commitIndex' = [commitIndex EXCEPT ![i] = 
                              IF m.commit > commitIndex[i]
                              THEN Min(m.commit, Len(log[i]))
                              ELSE commitIndex[i]]
            /\ Reply(Message(MsgHeartbeatResp, i, j, currentTerm'[i], 0, 0, <<>>, 0, FALSE, FALSE), m)
            /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
            /\ UNCHANGED heartbeatTimeout
       ELSE /\ Reply(Message(MsgHeartbeatResp, i, j, currentTerm[i], 0, 0, <<>>, 0, FALSE, FALSE), m)
            /\ UNCHANGED vars

HandleHeartbeatResponse(i, j, m) ==
    /\ m.type = MsgHeartbeatResp
    /\ m.to = i
    /\ m.from = j
    /\ state[i] = StateLeader
    /\ UNCHANGED vars

ReceiveMessage(m) ==
    /\ m \in messages
    /\ \/ /\ m.type = MsgPreVote
          /\ HandlePreVote(m.to, m.from, m)
       \/ /\ m.type = MsgPreVoteResp
          /\ HandlePreVoteResponse(m.to, m.from, m)
       \/ /\ m.type = MsgVote
          /\ HandleVote(m.to, m.from, m)
       \/ /\ m.type = MsgVoteResp
          /\ HandleVoteResponse(m.to, m.from, m)
       \/ /\ m.type = MsgApp
          /\ HandleAppendEntries(m.to, m.from, m)
       \/ /\ m.type = MsgAppResp
          /\ HandleAppendEntriesResponse(m.to, m.from, m)
       \/ /\ m.type = MsgHeartbeat
          /\ HandleHeartbeat(m.to, m.from, m)
       \/ /\ m.type = MsgHeartbeatResp
          /\ HandleHeartbeatResponse(m.to, m.from, m)
    /\ Discard(m)

Timeout(i) ==
    \/ ElectionTimeout(i)
    \/ SendHeartbeat(i)

DropMessage(m) ==
    /\ m \in messages
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

DuplicateMessage(m) ==
    /\ m \in messages
    /\ Send(m)
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

Next ==
    \/ \E i \in Servers : Timeout(i)
    \/ \E m \in messages : ReceiveMessage(m)
    \/ \E i \in Servers, data \in 1..3 : ClientRequest(i, data)
    \/ \E i, j \in Servers : SendAppendEntries(i, j)
    \/ \E m \in messages : DropMessage(m)
    \/ \E m \in messages : DuplicateMessage(m)

Spec == Init /\ [][Next]_vars

====