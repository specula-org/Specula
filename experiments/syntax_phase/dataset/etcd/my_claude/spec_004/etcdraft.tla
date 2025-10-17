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

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term
LastIndex(xlog) == Len(xlog)

IsUpToDate(i, j) ==
    \/ LastTerm(log[i]) > LastTerm(log[j])
    \/ /\ LastTerm(log[i]) = LastTerm(log[j])
       /\ LastIndex(log[i]) >= LastIndex(log[j])

Send(m) == messages' = messages \cup {m}

Reply(m, response) == Send(response)

DropMessage(m) == messages' = messages \ {m}

Receive(m) == 
    /\ m \in messages
    /\ DropMessage(m)

ElectionTimeout(i) ==
    /\ electionTimeout[i] = TRUE
    /\ state[i] \in {StateFollower, StateCandidate, StatePreCandidate}
    /\ state' = [state EXCEPT ![i] = StatePreCandidate]
    /\ currentTerm' = currentTerm
    /\ votedFor' = votedFor
    /\ votes' = [votes EXCEPT ![i] = {}]
    /\ Send(Message(MsgHup, i, i, 0, 0, 0, <<>>, 0, FALSE, FALSE))
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, electionTimeout, heartbeatTimeout>>

HandleMsgHup(i) ==
    /\ \E m \in messages : 
        /\ m.type = MsgHup
        /\ m.to = i
        /\ Receive(m)
        /\ IF state[i] = StatePreCandidate
           THEN /\ LET term == currentTerm[i] + 1
                   IN /\ \A j \in Servers \ {i} :
                           Send(Message(MsgPreVote, i, j, term, LastTerm(log[i]), LastIndex(log[i]), <<>>, 0, FALSE, FALSE))
                      /\ votes' = [votes EXCEPT ![i] = {i}]
                      /\ UNCHANGED <<currentTerm, votedFor, state>>
           ELSE /\ state' = [state EXCEPT ![i] = StateCandidate]
                /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
                /\ votedFor' = [votedFor EXCEPT ![i] = i]
                /\ votes' = [votes EXCEPT ![i] = {i}]
                /\ \A j \in Servers \ {i} :
                     Send(Message(MsgVote, i, j, currentTerm[i] + 1, LastTerm(log[i]), LastIndex(log[i]), <<>>, 0, FALSE, FALSE))
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, electionTimeout, heartbeatTimeout>>

HandleMsgPreVote(i) ==
    /\ \E m \in messages :
        /\ m.type = MsgPreVote
        /\ m.to = i
        /\ Receive(m)
        /\ LET grant == /\ m.term > currentTerm[i]
                        /\ IsUpToDate(m.from, i)
           IN Reply(m, Message(MsgPreVoteResp, i, m.from, m.term, 0, 0, <<>>, 0, grant, ~grant))
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

HandleMsgPreVoteResp(i) ==
    /\ \E m \in messages :
        /\ m.type = MsgPreVoteResp
        /\ m.to = i
        /\ state[i] = StatePreCandidate
        /\ Receive(m)
        /\ IF m.voteGranted
           THEN /\ votes' = [votes EXCEPT ![i] = votes[i] \cup {m.from}]
                /\ IF Cardinality(votes'[i]) * 2 > Cardinality(Servers)
                   THEN /\ state' = [state EXCEPT ![i] = StateCandidate]
                        /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
                        /\ LET newVotedFor == [votedFor EXCEPT ![i] = i]
                               newVotes == [votes' EXCEPT ![i] = {i}]
                           IN /\ votedFor' = newVotedFor
                              /\ votes' = newVotes
                              /\ \A j \in Servers \ {i} :
                                   Send(Message(MsgVote, i, j, currentTerm'[i], LastTerm(log[i]), LastIndex(log[i]), <<>>, 0, FALSE, FALSE))
                   ELSE /\ UNCHANGED <<state, currentTerm, votedFor>>
           ELSE /\ votes' = votes
                /\ UNCHANGED <<state, currentTerm, votedFor>>
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, electionTimeout, heartbeatTimeout>>

HandleMsgVote(i) ==
    /\ \E m \in messages :
        /\ m.type = MsgVote
        /\ m.to = i
        /\ Receive(m)
        /\ LET newCurrentTerm == IF m.term > currentTerm[i] THEN [currentTerm EXCEPT ![i] = m.term] ELSE currentTerm
               newVotedFor == IF m.term > currentTerm[i] THEN [votedFor EXCEPT ![i] = None] ELSE votedFor
               newState == IF m.term > currentTerm[i] THEN [state EXCEPT ![i] = StateFollower] ELSE state
               grant == /\ m.term >= newCurrentTerm[i]
                        /\ newVotedFor[i] \in {None, m.from}
                        /\ IsUpToDate(m.from, i)
           IN /\ currentTerm' = newCurrentTerm
              /\ state' = newState
              /\ IF grant
                 THEN votedFor' = [newVotedFor EXCEPT ![i] = m.from]
                 ELSE votedFor' = newVotedFor
              /\ Reply(m, Message(MsgVoteResp, i, m.from, newCurrentTerm[i], 0, 0, <<>>, 0, grant, ~grant))
    /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

HandleMsgVoteResp(i) ==
    /\ \E m \in messages :
        /\ m.type = MsgVoteResp
        /\ m.to = i
        /\ state[i] = StateCandidate
        /\ m.term = currentTerm[i]
        /\ Receive(m)
        /\ IF m.voteGranted
           THEN /\ votes' = [votes EXCEPT ![i] = votes[i] \cup {m.from}]
                /\ IF Cardinality(votes'[i]) * 2 > Cardinality(Servers)
                   THEN /\ state' = [state EXCEPT ![i] = StateLeader]
                        /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> LastIndex(log[i]) + 1]]
                        /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
                        /\ \A j \in Servers \ {i} :
                             Send(Message(MsgHeartbeat, i, j, currentTerm[i], 0, 0, <<>>, commitIndex[i], FALSE, FALSE))
                   ELSE /\ UNCHANGED <<state, nextIndex, matchIndex>>
           ELSE /\ votes' = votes
                /\ UNCHANGED <<state, nextIndex, matchIndex>>
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, electionTimeout, heartbeatTimeout>>

HandleMsgApp(i) ==
    /\ \E m \in messages :
        /\ m.type = MsgApp
        /\ m.to = i
        /\ Receive(m)
        /\ LET newCurrentTerm == IF m.term > currentTerm[i] THEN [currentTerm EXCEPT ![i] = m.term] ELSE currentTerm
               newVotedFor == IF m.term > currentTerm[i] THEN [votedFor EXCEPT ![i] = None] ELSE votedFor
               newState == IF m.term > currentTerm[i] THEN [state EXCEPT ![i] = StateFollower] ELSE state
               logOk == \/ m.index = 0
                        \/ /\ m.index > 0
                           /\ m.index <= Len(log[i])
                           /\ log[i][m.index].term = m.logTerm
           IN /\ currentTerm' = newCurrentTerm
              /\ votedFor' = newVotedFor
              /\ state' = newState
              /\ IF /\ m.term = newCurrentTerm[i]
                    /\ logOk
                 THEN /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, m.index) \o m.entries]
                      /\ commitIndex' = [commitIndex EXCEPT ![i] = 
                           IF m.commit > commitIndex[i]
                           THEN Min(m.commit, Len(log'[i]))
                           ELSE commitIndex[i]]
                      /\ Reply(m, Message(MsgAppResp, i, m.from, newCurrentTerm[i], 0, Len(log'[i]), <<>>, 0, FALSE, FALSE))
                 ELSE /\ Reply(m, Message(MsgAppResp, i, m.from, newCurrentTerm[i], 0, 0, <<>>, 0, FALSE, TRUE))
                      /\ UNCHANGED <<log, commitIndex>>
    /\ UNCHANGED <<nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

HandleMsgAppResp(i) ==
    /\ \E m \in messages :
        /\ m.type = MsgAppResp
        /\ m.to = i
        /\ state[i] = StateLeader
        /\ m.term = currentTerm[i]
        /\ Receive(m)
        /\ IF m.reject
           THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.from] = IF nextIndex[i][m.from] > 1 THEN nextIndex[i][m.from] - 1 ELSE 1]]
                /\ UNCHANGED <<matchIndex, commitIndex>>
           ELSE /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![m.from] = m.index + 1]]
                /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![m.from] = m.index]]
                /\ LET agreeIndexes == {matchIndex'[i][j] : j \in Servers}
                   IN commitIndex' = [commitIndex EXCEPT ![i] = 
                        LET maxCommittable == CHOOSE idx \in agreeIndexes \cup {commitIndex[i]} :
                            /\ \A other \in agreeIndexes \cup {commitIndex[i]} :
                                /\ other <= idx
                                /\ (other > commitIndex[i]) => 
                                   (/\ Cardinality({j \in Servers : matchIndex'[i][j] >= other}) * 2 > Cardinality(Servers)
                                    /\ other <= Len(log[i])
                                    /\ log[i][other].term = currentTerm[i])
                        IN maxCommittable]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, votes, electionTimeout, heartbeatTimeout>>

HandleMsgHeartbeat(i) ==
    /\ \E m \in messages :
        /\ m.type = MsgHeartbeat
        /\ m.to = i
        /\ Receive(m)
        /\ LET newCurrentTerm == IF m.term > currentTerm[i] THEN [currentTerm EXCEPT ![i] = m.term] ELSE currentTerm
               newVotedFor == IF m.term > currentTerm[i] THEN [votedFor EXCEPT ![i] = None] ELSE votedFor
               newState == IF m.term > currentTerm[i] THEN [state EXCEPT ![i] = StateFollower] ELSE state
           IN /\ currentTerm' = newCurrentTerm
              /\ votedFor' = newVotedFor
              /\ state' = newState
              /\ commitIndex' = [commitIndex EXCEPT ![i] = 
                   IF m.commit > commitIndex[i]
                   THEN Min(m.commit, Len(log[i]))
                   ELSE commitIndex[i]]
              /\ Reply(m, Message(MsgHeartbeatResp, i, m.from, newCurrentTerm[i], 0, 0, <<>>, 0, FALSE, FALSE))
              /\ electionTimeout' = [electionTimeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<log, nextIndex, matchIndex, votes, heartbeatTimeout>>

HandleMsgHeartbeatResp(i) ==
    /\ \E m \in messages :
        /\ m.type = MsgHeartbeatResp
        /\ m.to = i
        /\ state[i] = StateLeader
        /\ Receive(m)
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

HandleMsgProp(i) ==
    /\ \E m \in messages :
        /\ m.type = MsgProp
        /\ m.to = i
        /\ Receive(m)
        /\ IF state[i] = StateLeader
           THEN /\ log' = [log EXCEPT ![i] = Append(log[i], Entry(currentTerm[i], Len(log[i]) + 1, m.entries))]
                /\ \A j \in Servers \ {i} :
                     LET prevIndex == nextIndex[i][j] - 1
                         prevTerm == IF prevIndex > 0 THEN log[i][prevIndex].term ELSE 0
                         entries == SubSeq(log'[i], nextIndex[i][j], Len(log'[i]))
                     IN Send(Message(MsgApp, i, j, currentTerm[i], prevTerm, prevIndex, entries, commitIndex[i], FALSE, FALSE))
           ELSE /\ UNCHANGED log
    /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout, heartbeatTimeout>>

HeartbeatTimeout(i) ==
    /\ heartbeatTimeout[i] = TRUE
    /\ state[i] = StateLeader
    /\ \A j \in Servers \ {i} :
         Send(Message(MsgHeartbeat, i, j, currentTerm[i], 0, 0, <<>>, commitIndex[i], FALSE, FALSE))
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, electionTimeout>>

TimeoutElection(i) ==
    /\ electionTimeout' = [electionTimeout EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, messages, heartbeatTimeout>>

TimeoutHeartbeat(i) ==
    /\ heartbeatTimeout' = [heartbeatTimeout EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<currentTerm, votedFor, log, state, commitIndex, nextIndex, matchIndex, votes, messages, electionTimeout>>

Next ==
    \/ \E i \in Servers : ElectionTimeout(i)
    \/ \E i \in Servers : HandleMsgHup(i)
    \/ \E i \in Servers : HandleMsgPreVote(i)
    \/ \E i \in Servers : HandleMsgPreVoteResp(i)
    \/ \E i \in Servers : HandleMsgVote(i)
    \/ \E i \in Servers : HandleMsgVoteResp(i)
    \/ \E i \in Servers : HandleMsgApp(i)
    \/ \E i \in Servers : HandleMsgAppResp(i)
    \/ \E i \in Servers : HandleMsgHeartbeat(i)
    \/ \E i \in Servers : HandleMsgHeartbeatResp(i)
    \/ \E i \in Servers : HandleMsgProp(i)
    \/ \E i \in Servers : HeartbeatTimeout(i)
    \/ \E i \in Servers : TimeoutElection(i)
    \/ \E i \in Servers : TimeoutHeartbeat(i)

Spec == Init /\ [][Next]_vars

====