---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Servers, DefaultValue, Nil

ASSUME IsFiniteSet(Servers)
ASSUME Nil \notin Servers
ASSUME DefaultValue \notin Servers

NodeState == {"Follower", "Candidate", "Leader", "PreCandidate"}
MsgType == {"MsgApp", "MsgAppResp", "MsgPreVote", "MsgPreVoteResp", "MsgVote", "MsgVoteResp"}

Quorum == (Cardinality(Servers) \div 2) + 1

LastLogIndex(log) == Len(log)
LastLogTerm(log) == IF Len(log) = 0 THEN 0 ELSE log[Len(log)][1]

isUpToDate(myLog, candLastLogIndex, candLastLogTerm) ==
    LET myLastLogTerm == LastLogTerm(myLog)
        myLastLogIndex == LastLogIndex(myLog)
    IN (candLastLogTerm > myLastLogTerm) \/
       (candLastLogTerm = myLastLogTerm /\ candLastLogIndex >= myLastLogIndex)

max(a, b) == IF a >= b THEN a ELSE b
min(a, b) == IF a <= b THEN a ELSE b

VARIABLES
    currentTerm,
    votedFor,
    state,
    log,
    commitIndex,
    leader,
    votesGranted,
    nextIndex,
    matchIndex,
    messages

vars == << currentTerm, votedFor, state, log, commitIndex, leader,
           votesGranted, nextIndex, matchIndex, messages >>

MessageRecord == [
    type         : MsgType,
    from         : Servers,
    to           : Servers,
    term         : Nat,
    \* MsgApp / MsgAppResp
    prevLogIndex : Nat,
    prevLogTerm  : Nat,
    entries      : Seq(Nat \X {DefaultValue}),
    leaderCommit : Nat,
    matchIndex   : Nat,
    success      : BOOLEAN,
    \* MsgVote / MsgPreVote
    lastLogIndex : Nat,
    lastLogTerm  : Nat
]

TypeOK ==
    /\ currentTerm \in [Servers -> Nat]
    /\ votedFor \in [Servers -> Servers \cup {Nil}]
    /\ state \in [Servers -> NodeState]
    /\ log \in [Servers -> Seq(Nat \X {DefaultValue})]
    /\ commitIndex \in [Servers -> Nat]
    /\ leader \in [Servers -> Servers \cup {Nil}]
    /\ votesGranted \in [Servers -> SUBSET Servers]
    /\ nextIndex \in [Servers -> [Servers -> Nat]]
    /\ matchIndex \in [Servers -> [Servers -> Nat]]
    /\ IsABag(messages)

Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ state = [s \in Servers |-> "Follower"]
    /\ log = [s \in Servers |-> << >>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ leader = [s \in Servers |-> Nil]
    /\ votesGranted = [s \in Servers |-> {}]
    /\ nextIndex = [s \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [s \in Servers |-> [j \in Servers |-> 0]]
    /\ messages = EmptyBag

\* A node's election timer times out, causing it to start a pre-election campaign.
Timeout(i) ==
    /\ state[i] \in {"Follower", "Candidate", "PreCandidate"}
    /\ state' = [state EXCEPT ![i] = "PreCandidate"]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ LET
           nextTerm == currentTerm[i] + 1
           lli == LastLogIndex(log[i])
           llt == LastLogTerm(log[i])
           newMsgs == { [ type         |-> "MsgPreVote",
                          from         |-> i,
                          to           |-> j,
                          term         |-> nextTerm,
                          lastLogIndex |-> lli,
                          lastLogTerm  |-> llt,
                          prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>,
                          leaderCommit |-> 0, matchIndex |-> 0, success |-> FALSE
                        ] : j \in Servers \ {i} }
       IN messages' = messages (+) SetToBag(newMsgs)
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, leader, nextIndex, matchIndex>>

\* A client sends a proposal to the leader.
ClientRequest(v) ==
    \E i \in Servers:
        /\ state[i] = "Leader"
        /\ LET newEntry == <<currentTerm[i], v>>
           IN log' = [log EXCEPT ![i] = Append(log[i], newEntry)]
        /\ UNCHANGED <<currentTerm, votedFor, state, commitIndex, leader,
                       votesGranted, nextIndex, matchIndex, messages>>

\* The leader sends append entries or heartbeats to its followers.
LeaderSendAppend(i) ==
    /\ state[i] = "Leader"
    /\ \E j \in Servers \ {i}:
        /\ LET
               ni == nextIndex[i][j]
               prevLogIndex == ni - 1
               prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex][1] ELSE 0
               entriesToSend == IF LastLogIndex(log[i]) >= ni
                                THEN SubSeq(log[i], ni, Len(log[i]))
                                ELSE << >>
               msg == [ type         |-> "MsgApp",
                        from         |-> i,
                        to           |-> j,
                        term         |-> currentTerm[i],
                        prevLogIndex |-> prevLogIndex,
                        prevLogTerm  |-> prevLogTerm,
                        entries      |-> entriesToSend,
                        leaderCommit |-> commitIndex[i],
                        success      |-> FALSE, matchIndex |-> 0,
                        lastLogIndex |-> 0, lastLogTerm |-> 0
                      ]
           IN messages' = messages (+) SetToBag({msg})
    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader,
                   votesGranted, nextIndex, matchIndex>>

\* A node processes a received message.
HandleMessage(i) ==
    \E m \in DOMAIN messages:
        /\ m.to = i
        /\ LET
               \* If message has a higher term, become a follower.
               BecomeFollower(newTerm, newLeader) ==
                   /\ currentTerm' = [currentTerm EXCEPT ![i] = newTerm]
                   /\ state' = [state EXCEPT ![i] = "Follower"]
                   /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                   /\ leader' = [leader EXCEPT ![i] = newLeader]
                   /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
           IN
           \/ /\ m.term > currentTerm[i]
              /\ BecomeFollower(m.term, IF m.type = "MsgApp" THEN m.from ELSE Nil)
              /\ messages' = messages (-) SetToBag({m})
              /\ UNCHANGED <<log, commitIndex, nextIndex, matchIndex>>

           \/ /\ m.term < currentTerm[i]
              /\ messages' = messages (-) SetToBag({m})
              /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader,
                             votesGranted, nextIndex, matchIndex>>

           \/ /\ m.term = currentTerm[i]
              /\ CASE m.type = "MsgPreVote" ->
                    /\ LET grantVote == isUpToDate(log[i], m.lastLogIndex, m.lastLogTerm)
                           respMsg == [m EXCEPT !.type = "MsgPreVoteResp", !.from = i, !.to = m.from, !.success = grantVote]
                       IN messages' = (messages (-) SetToBag({m})) (+) SetToBag({respMsg})
                    /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader, votesGranted, nextIndex, matchIndex>>

                 [] m.type = "MsgPreVoteResp" ->
                    /\ IF state[i] = "PreCandidate"
                       THEN LET newVotes == IF m.success THEN votesGranted[i] \cup {m.from} ELSE votesGranted[i]
                            IN \/ /\ Cardinality(newVotes) < Quorum
                                  /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                                  /\ messages' = messages (-) SetToBag({m})
                                  /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader, nextIndex, matchIndex>>
                               \/ /\ Cardinality(newVotes) >= Quorum
                                  /\ state' = [state EXCEPT ![i] = "Candidate"]
                                  /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
                                  /\ votedFor' = [votedFor EXCEPT ![i] = i]
                                  /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
                                  /\ LET newTerm == currentTerm[i] + 1
                                         lli == LastLogIndex(log[i])
                                         llt == LastLogTerm(log[i])
                                         newMsgs == { [ type |-> "MsgVote", from |-> i, to |-> j, term |-> newTerm,
                                                        lastLogIndex |-> lli, lastLogTerm |-> llt,
                                                        prevLogIndex |-> 0, prevLogTerm |-> 0, entries |-> <<>>,
                                                        leaderCommit |-> 0, matchIndex |-> 0, success |-> FALSE
                                                      ] : j \in Servers \ {i} }
                                     IN messages' = (messages (-) SetToBag({m})) (+) SetToBag(newMsgs)
                                  /\ UNCHANGED <<log, commitIndex, leader, nextIndex, matchIndex>>
                       ELSE /\ messages' = messages (-) SetToBag({m})
                            /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader, votesGranted, nextIndex, matchIndex>>

                 [] m.type = "MsgVote" ->
                    /\ LET grantVote == (votedFor[i] \in {Nil, m.from}) /\ isUpToDate(log[i], m.lastLogIndex, m.lastLogTerm)
                           respMsg == [m EXCEPT !.type = "MsgVoteResp", !.from = i, !.to = m.from, !.success = grantVote]
                       IN /\ messages' = (messages (-) SetToBag({m})) (+) SetToBag({respMsg})
                          /\ IF grantVote THEN votedFor' = [votedFor EXCEPT ![i] = m.from]
                                         ELSE UNCHANGED votedFor
                    /\ UNCHANGED <<currentTerm, state, log, commitIndex, leader, votesGranted, nextIndex, matchIndex>>

                 [] m.type = "MsgVoteResp" ->
                    /\ IF state[i] = "Candidate"
                       THEN LET newVotes == IF m.success THEN votesGranted[i] \cup {m.from} ELSE votesGranted[i]
                            IN \/ /\ Cardinality(newVotes) < Quorum
                                  /\ votesGranted' = [votesGranted EXCEPT ![i] = newVotes]
                                  /\ messages' = messages (-) SetToBag({m})
                                  /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader, nextIndex, matchIndex>>
                               \/ /\ Cardinality(newVotes) >= Quorum
                                  /\ state' = [state EXCEPT ![i] = "Leader"]
                                  /\ leader' = [leader EXCEPT ![i] = i]
                                  /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Servers |-> LastLogIndex(log[i]) + 1]]
                                  /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
                                  /\ messages' = messages (-) SetToBag({m})
                                  /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, votesGranted>>
                       ELSE /\ messages' = messages (-) SetToBag({m})
                            /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader, votesGranted, nextIndex, matchIndex>>

                 [] m.type = "MsgApp" ->
                    /\ LET logOK == m.prevLogIndex = 0 \/
                                  (m.prevLogIndex <= Len(log[i]) /\ log[i][m.prevLogIndex][1] = m.prevLogTerm)
                       IN \/ /\ logOK
                             /\ LET newLog == Append(SubSeq(log[i], 1, m.prevLogIndex), m.entries)
                                    newLastIndex == LastLogIndex(newLog)
                                    newCommitIndex == max(commitIndex[i], min(m.leaderCommit, newLastIndex))
                                    respMsg == [m EXCEPT !.type = "MsgAppResp", !.from = i, !.to = m.from, !.success = TRUE, !.matchIndex = newLastIndex]
                                IN /\ log' = [log EXCEPT ![i] = newLog]
                                   /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
                                   /\ messages' = (messages (-) SetToBag({m})) (+) SetToBag({respMsg})
                          \/ /\ ~logOK
                             /\ LET respMsg == [m EXCEPT !.type = "MsgAppResp", !.from = i, !.to = m.from, !.success = FALSE, !.matchIndex = 0]
                                IN messages' = (messages (-) SetToBag({m})) (+) SetToBag({respMsg})
                             /\ UNCHANGED <<log, commitIndex>>
                    /\ state' = [state EXCEPT ![i] = "Follower"]
                    /\ leader' = [leader EXCEPT ![i] = m.from]
                    /\ UNCHANGED <<currentTerm, votedFor, votesGranted, nextIndex, matchIndex>>

                 [] m.type = "MsgAppResp" ->
                    /\ IF state[i] = "Leader"
                       THEN /\ LET follower == m.from
                               IN \/ /\ m.success
                                     /\ LET newMatchIndex == [matchIndex[i] EXCEPT ![follower] = max(matchIndex[i][follower], m.matchIndex)]
                                            newNextIndex == [nextIndex[i] EXCEPT ![follower] = m.matchIndex + 1]
                                            possibleCommits == { n \in commitIndex[i]+1..LastLogIndex(log[i]) :
                                                                   /\ Cardinality({ s \in Servers : newMatchIndex[s] >= n }) >= Quorum
                                                                   /\ log[i][n][1] = currentTerm[i]
                                                               }
                                            newCommit == IF possibleCommits = {} THEN commitIndex[i] ELSE SetMax(possibleCommits)
                                        IN /\ matchIndex' = [matchIndex EXCEPT ![i] = newMatchIndex]
                                           /\ nextIndex' = [nextIndex EXCEPT ![i] = newNextIndex]
                                           /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommit]
                                  \/ /\ ~m.success
                                     /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![follower] = max(1, nextIndex[i][follower] - 1)]]
                                     /\ UNCHANGED <<matchIndex, commitIndex>>
                              /\ messages' = messages (-) SetToBag({m})
                              /\ UNCHANGED <<currentTerm, votedFor, state, log, leader, votesGranted>>
                       ELSE /\ messages' = messages (-) SetToBag({m})
                            /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader, votesGranted, nextIndex, matchIndex>>

\* A message in the network is lost.
DropMessage ==
    \E m \in DOMAIN messages:
        /\ messages' = messages (-) SetToBag({m})
        /\ UNCHANGED <<currentTerm, votedFor, state, log, commitIndex, leader,
                       votesGranted, nextIndex, matchIndex>>

Next ==
    \/ \E i \in Servers:
        \/ Timeout(i)
        \/ LeaderSendAppend(i)
        \/ HandleMessage(i)
    \/ ClientRequest(DefaultValue)
    \/ DropMessage

Spec == Init /\ [][Next]_vars

=============================================================================
