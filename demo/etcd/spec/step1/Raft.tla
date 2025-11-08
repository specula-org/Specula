---- MODULE Raft ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Server,          \* Set of server IDs
    MaxTerm,         \* Maximum term number
    MaxLogLen,       \* Maximum log length
    None             \* Constant for no leader (0)

VARIABLES 
    \* Core state variables from the analysis
    state,                      \* Server state (follower/candidate/leader)
    currentTerm,                \* Latest term server has seen
    votedFor,                   \* CandidateId that received vote in current term
    log,                        \* Log entries
    commitIndex,                \* Index of highest log entry known to be committed
    leaderId,                   \* Current leader ID
    \* Progress tracking
    matchIndex,                 \* For each server, index of highest log entry known to be replicated
    nextIndex,                  \* For each server, index of next log entry to send
    votesGranted,               \* Votes received in current election
    \* Additional state
    pendingConfIndex,           \* Index of pending configuration change
    uncommittedSize,            \* Size of uncommitted entries
    leadTransferee,             \* Target of leadership transfer
    isLearner,                  \* Whether node is a learner
    electionElapsed,            \* Ticks since last election timeout reset
    heartbeatElapsed,           \* Ticks since last heartbeat (leader only)
    randomizedElectionTimeout,  \* Current election timeout value
    messages                    \* Set of messages in transit

vars == <<state, currentTerm, votedFor, log, commitIndex, leaderId, 
          matchIndex, nextIndex, votesGranted, pendingConfIndex, 
          uncommittedSize, leadTransferee, isLearner, electionElapsed,
          heartbeatElapsed, randomizedElectionTimeout, messages>>

\* Message types
MsgVote == "MsgVote"
MsgVoteResp == "MsgVoteResp"
MsgPreVote == "MsgPreVote"
MsgPreVoteResp == "MsgPreVoteResp"
MsgApp == "MsgApp"
MsgAppResp == "MsgAppResp"
MsgHeartbeat == "MsgHeartbeat"
MsgHeartbeatResp == "MsgHeartbeatResp"
MsgSnap == "MsgSnap"
MsgTimeoutNow == "MsgTimeoutNow"
MsgHup == "MsgHup"
MsgBeat == "MsgBeat"
MsgProp == "MsgProp"

\* State types
StateFollower == "StateFollower"
StateCandidate == "StateCandidate"
StateLeader == "StateLeader"
StatePreCandidate == "StatePreCandidate"

\* Helper functions
Min(a, b) == IF a < b THEN a ELSE b
Max(a, b) == IF a > b THEN a ELSE b

LastLogIndex(s) == Len(log[s])
LastLogTerm(s) == IF Len(log[s]) = 0 THEN 0 ELSE log[s][Len(log[s])].term

\* Check if log is up to date
IsLogUpToDate(s, lastLogTerm, lastLogIndex) ==
    \/ lastLogTerm > LastLogTerm(s)
    \/ /\ lastLogTerm = LastLogTerm(s)
       /\ lastLogIndex >= LastLogIndex(s)

\* Count votes
CountVotes(s) == Cardinality({v \in Server : votesGranted[s][v]})


Init == 
    /\ state = [s \in Server |-> StateFollower]
    /\ currentTerm = [s \in Server |-> 0]
    /\ votedFor = [s \in Server |-> None]
    /\ log = [s \in Server |-> <<>>]
    /\ commitIndex = [s \in Server |-> 0]
    /\ leaderId = [s \in Server |-> None]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ votesGranted = [s \in Server |-> [t \in Server |-> FALSE]]
    /\ pendingConfIndex = [s \in Server |-> 0]
    /\ uncommittedSize = [s \in Server |-> 0]
    /\ leadTransferee = [s \in Server |-> None]
    /\ isLearner = [s \in Server |-> FALSE]
    /\ electionElapsed = [s \in Server |-> 0]
    /\ heartbeatElapsed = [s \in Server |-> 0]
    /\ randomizedElectionTimeout = [s \in Server |-> 10]
    /\ messages = {}

\* Core function: becomeFollower
BecomeFollower(s, term, leader) ==
    /\ state' = [state EXCEPT ![s] = StateFollower]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = term]
    /\ votedFor' = [votedFor EXCEPT ![s] = IF term > currentTerm[s] THEN None ELSE votedFor[s]]
    /\ leaderId' = [leaderId EXCEPT ![s] = leader]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = [t \in Server |-> FALSE]]
    /\ leadTransferee' = [leadTransferee EXCEPT ![s] = None]
    /\ uncommittedSize' = [uncommittedSize EXCEPT ![s] = 0]
    /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, pendingConfIndex, 
                   isLearner, randomizedElectionTimeout, messages>>

\* Core function: becomeCandidate
BecomeCandidate(s) ==
    /\ state[s] # StateLeader  \* Precondition check
    /\ state' = [state EXCEPT ![s] = StateCandidate]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = [t \in Server |-> IF t = s THEN TRUE ELSE FALSE]]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ leaderId' = [leaderId EXCEPT ![s] = None]
    /\ UNCHANGED <<log, commitIndex, matchIndex, nextIndex, pendingConfIndex,
                   uncommittedSize, leadTransferee, isLearner, heartbeatElapsed,
                   randomizedElectionTimeout, messages>>

\* Core function: becomePreCandidate
BecomePreCandidate(s) ==
    /\ state[s] # StateLeader  \* Precondition check
    /\ state' = [state EXCEPT ![s] = StatePreCandidate]
    /\ votesGranted' = [votesGranted EXCEPT ![s] = [t \in Server |-> FALSE]]
    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
    /\ leaderId' = [leaderId EXCEPT ![s] = None]
    /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, matchIndex, nextIndex,
                   pendingConfIndex, uncommittedSize, leadTransferee, isLearner,
                   heartbeatElapsed, randomizedElectionTimeout, messages>>

\* Core function: becomeLeader
BecomeLeader(s) ==
    /\ state[s] # StateFollower  \* Precondition check
    /\ state' = [state EXCEPT ![s] = StateLeader]
    /\ leaderId' = [leaderId EXCEPT ![s] = s]
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
    /\ nextIndex' = [nextIndex EXCEPT ![s] = [t \in Server |-> LastLogIndex(s) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![s] = [t \in Server |-> IF t = s THEN LastLogIndex(s) ELSE 0]]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![s] = LastLogIndex(s)]
    \* Append empty entry
    /\ log' = [log EXCEPT ![s] = Append(log[s], [term |-> currentTerm[s], data |-> <<>>])]
    /\ messages' = messages \cup {[type |-> MsgAppResp, 
                                   from |-> s, 
                                   to |-> s, 
                                   term |-> currentTerm[s],
                                   index |-> LastLogIndex(s) + 1]}
    /\ UNCHANGED <<currentTerm, votedFor, commitIndex, votesGranted,
                   uncommittedSize, leadTransferee, isLearner, electionElapsed,
                   randomizedElectionTimeout>>

\* Core function: campaign
Campaign(s, campaignType) ==
    /\ \/ /\ campaignType = "PreElection"
          /\ BecomePreCandidate(s)
          /\ LET term == currentTerm[s] + 1
             IN messages' = messages \cup 
                {[type |-> MsgPreVote,
                  from |-> s,
                  to |-> t,
                  term |-> term,
                  logTerm |-> LastLogTerm(s),
                  index |-> LastLogIndex(s)] : t \in Server \ {s}}
       \/ /\ campaignType = "Election"
          /\ BecomeCandidate(s)
          /\ messages' = messages \cup 
             {[type |-> MsgVote,
               from |-> s,
               to |-> t,
               term |-> currentTerm'[s],
               logTerm |-> LastLogTerm(s),
               index |-> LastLogIndex(s)] : t \in Server \ {s}}

                 
\* Helper actions for vote handling
HandleVote(s, m) ==
    LET canVote == \/ votedFor[s] = m.from
                   \/ /\ votedFor[s] = None
                      /\ leaderId[s] = None
                   \/ /\ m.type = MsgPreVote
                      /\ m.term > currentTerm[s]
    IN IF /\ canVote
          /\ IsLogUpToDate(s, m.logTerm, m.index)
       THEN /\ messages' = messages \cup {[type |-> IF m.type = MsgVote THEN MsgVoteResp ELSE MsgPreVoteResp,
                                           from |-> s, to |-> m.from, term |-> m.term]}
            /\ IF m.type = MsgVote
               THEN /\ votedFor' = [votedFor EXCEPT ![s] = m.from]
                    /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
               ELSE UNCHANGED <<votedFor, electionElapsed>>
            /\ UNCHANGED <<state, currentTerm, log, commitIndex, leaderId, matchIndex, nextIndex,
                           votesGranted, pendingConfIndex, uncommittedSize, leadTransferee,
                           isLearner, heartbeatElapsed, randomizedElectionTimeout>>
       ELSE /\ messages' = messages \cup {[type |-> IF m.type = MsgVote THEN MsgVoteResp ELSE MsgPreVoteResp,
                                           from |-> s, to |-> m.from, term |-> currentTerm[s], reject |-> TRUE]}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                           matchIndex, nextIndex, votesGranted, pendingConfIndex,
                           uncommittedSize, leadTransferee, isLearner, electionElapsed,
                           heartbeatElapsed, randomizedElectionTimeout>>


\* Core function: maybeCommit
MaybeCommit(s) ==
    /\ state[s] = StateLeader
    /\ LET newCommitIndex == CHOOSE i \in 1..Len(log[s]) :
           /\ i > commitIndex[s]
           /\ log[s][i].term = currentTerm[s]
           /\ Cardinality({t \in Server : matchIndex[s][t] >= i}) * 2 > Cardinality(Server)
           /\ \A j \in (i+1)..Len(log[s]) : 
              ~(/\ log[s][j].term = currentTerm[s]
                /\ Cardinality({t \in Server : matchIndex[s][t] >= j}) * 2 > Cardinality(Server))
       IN /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
          /\ UNCHANGED <<state, currentTerm, votedFor, log, leaderId, matchIndex, nextIndex,
                         votesGranted, pendingConfIndex, uncommittedSize, leadTransferee,
                         isLearner, electionElapsed, heartbeatElapsed, randomizedElectionTimeout, messages>>


HandleAppResp(s, m) ==
    IF m.reject
    THEN /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = Max(1, m.rejectHint)]
         /\ messages' = messages \cup 
            {[type |-> MsgApp,
              from |-> s,
              to |-> m.from,
              term |-> currentTerm[s],
              prevLogIndex |-> nextIndex'[s][m.from] - 1,
              prevLogTerm |-> IF nextIndex'[s][m.from] > 1 
                               THEN log[s][nextIndex'[s][m.from] - 1].term 
                               ELSE 0,
              entries |-> SubSeq(log[s], nextIndex'[s][m.from], Len(log[s])),
              commit |-> commitIndex[s]]}
         /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                        matchIndex, votesGranted, pendingConfIndex, uncommittedSize,
                        leadTransferee, isLearner, electionElapsed, heartbeatElapsed,
                        randomizedElectionTimeout>>
    ELSE /\ matchIndex' = [matchIndex EXCEPT ![s][m.from] = m.index]
         /\ nextIndex' = [nextIndex EXCEPT ![s][m.from] = m.index + 1]
         /\ MaybeCommit(s)


\* Core function: handleHeartbeat
HandleHeartbeat(s, m) ==
    /\ commitIndex' = [commitIndex EXCEPT ![s] = Max(commitIndex[s], m.commit)]
    /\ messages' = messages \cup {[type |-> MsgHeartbeatResp, from |-> s, to |-> m.from, term |-> currentTerm[s]]}
    /\ UNCHANGED <<state, currentTerm, votedFor, log, leaderId, matchIndex, nextIndex,
                   votesGranted, pendingConfIndex, uncommittedSize, leadTransferee,
                   isLearner, heartbeatElapsed, randomizedElectionTimeout>>

                
HandleHeartbeatResp(s, m) ==
    IF matchIndex[s][m.from] < LastLogIndex(s)
    THEN messages' = messages \cup 
         {[type |-> MsgApp,
           from |-> s,
           to |-> m.from,
           term |-> currentTerm[s],
           prevLogIndex |-> nextIndex[s][m.from] - 1,
           prevLogTerm |-> IF nextIndex[s][m.from] > 1 
                            THEN log[s][nextIndex[s][m.from] - 1].term 
                            ELSE 0,
           entries |-> SubSeq(log[s], nextIndex[s][m.from], Len(log[s])),
           commit |-> commitIndex[s]]}
    ELSE UNCHANGED messages
    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                   matchIndex, nextIndex, votesGranted, pendingConfIndex,
                   uncommittedSize, leadTransferee, isLearner, electionElapsed,
                   heartbeatElapsed, randomizedElectionTimeout>>


\* Core function: stepLeader
StepLeader(s, m) ==
    \/ /\ m.type = MsgBeat
       /\ messages' = messages \cup 
          {[type |-> MsgHeartbeat,
            from |-> s,
            to |-> t,
            term |-> currentTerm[s],
            commit |-> Min(matchIndex[s][t], commitIndex[s])] : t \in Server \ {s}}
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                      matchIndex, nextIndex, votesGranted, pendingConfIndex,
                      uncommittedSize, leadTransferee, isLearner, electionElapsed,
                      heartbeatElapsed, randomizedElectionTimeout>>
    \/ /\ m.type = MsgProp
       /\ leadTransferee[s] = None
       /\ LET newEntry == [term |-> currentTerm[s], data |-> m.data]
              newLog == Append(log[s], newEntry)
          IN /\ log' = [log EXCEPT ![s] = newLog]
             /\ messages' = messages \cup 
                {[type |-> MsgApp,
                  from |-> s,
                  to |-> t,
                  term |-> currentTerm[s],
                  prevLogIndex |-> nextIndex[s][t] - 1,
                  prevLogTerm |-> IF nextIndex[s][t] > 1 
                                   THEN log[s][nextIndex[s][t] - 1].term 
                                   ELSE 0,
                  entries |-> <<newEntry>>,
                  commit |-> commitIndex[s]] : t \in Server \ {s}}
             /\ UNCHANGED <<state, currentTerm, votedFor, commitIndex, leaderId,
                            matchIndex, nextIndex, votesGranted, pendingConfIndex,
                            uncommittedSize, leadTransferee, isLearner, electionElapsed,
                            heartbeatElapsed, randomizedElectionTimeout>>
    \/ /\ m.type = MsgAppResp
       /\ HandleAppResp(s, m)
    \/ /\ m.type = MsgHeartbeatResp
       /\ HandleHeartbeatResp(s, m)

\* Core function: poll
Poll(s, from, msgType, granted) ==
    /\ votesGranted' = [votesGranted EXCEPT ![s][from] = granted]
    /\ LET voteCount == CountVotes(s)
       IN IF voteCount * 2 > Cardinality(Server)
          THEN IF state[s] = StatePreCandidate
               THEN Campaign(s, "Election")
               ELSE BecomeLeader(s)
          ELSE IF (Cardinality(Server) - voteCount) * 2 >= Cardinality(Server)
               THEN BecomeFollower(s, currentTerm[s], None)
               ELSE UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                               matchIndex, nextIndex, pendingConfIndex, uncommittedSize,
                               leadTransferee, isLearner, electionElapsed, heartbeatElapsed,
                               randomizedElectionTimeout, messages>>

HandleVoteResp(s, m) ==
    Poll(s, m.from, m.type, ~m.reject)

                    
\* Core function: stepCandidate
StepCandidate(s, m) ==
    \/ /\ m.type = MsgProp
       /\ UNCHANGED vars  \* Drop proposal
    \/ /\ m.type \in {MsgApp, MsgHeartbeat}
       /\ BecomeFollower(s, m.term, m.from)
    \/ /\ m.type = IF state[s] = StatePreCandidate THEN MsgPreVoteResp ELSE MsgVoteResp
       /\ HandleVoteResp(s, m)



\* Core function: handleAppendEntries
HandleAppendEntries(s, m) ==
    /\ IF m.prevLogIndex < commitIndex[s]
       THEN /\ messages' = messages \cup {[type |-> MsgAppResp, from |-> s, to |-> m.from, 
                                           term |-> currentTerm[s], index |-> commitIndex[s]]}
            /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, matchIndex, 
                           nextIndex, votesGranted, pendingConfIndex, uncommittedSize, 
                           leadTransferee, isLearner, heartbeatElapsed, randomizedElectionTimeout>>
       ELSE IF /\ m.prevLogIndex = 0 
            \/ /\ m.prevLogIndex <= Len(log[s])
               /\ log[s][m.prevLogIndex].term = m.prevLogTerm
            THEN \* Accept the entries
                 /\ log' = [log EXCEPT ![s] = SubSeq(log[s], 1, m.prevLogIndex) \o m.entries]
                 /\ commitIndex' = [commitIndex EXCEPT ![s] = Min(m.commit, m.prevLogIndex + Len(m.entries))]
                 /\ messages' = messages \cup {[type |-> MsgAppResp, from |-> s, to |-> m.from,
                                                term |-> currentTerm[s], index |-> m.prevLogIndex + Len(m.entries)]}
                 /\ UNCHANGED <<state, currentTerm, votedFor, leaderId, matchIndex, nextIndex,
                                votesGranted, pendingConfIndex, uncommittedSize, leadTransferee,
                                isLearner, heartbeatElapsed, randomizedElectionTimeout>>
            ELSE \* Reject - find conflict
                 LET hintIndex == Min(m.prevLogIndex, Len(log[s]))
                     hintTerm == IF hintIndex > 0 /\ hintIndex <= Len(log[s]) 
                                 THEN log[s][hintIndex].term 
                                 ELSE 0
                 IN /\ messages' = messages \cup {[type |-> MsgAppResp, from |-> s, to |-> m.from,
                                                   term |-> currentTerm[s], index |-> m.prevLogIndex,
                                                   reject |-> TRUE, rejectHint |-> hintIndex, logTerm |-> hintTerm]}
                    /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                                   matchIndex, nextIndex, votesGranted, pendingConfIndex,
                                   uncommittedSize, leadTransferee, isLearner, heartbeatElapsed,
                                   randomizedElectionTimeout>>


\* Core function: stepFollower
StepFollower(s, m) ==
    \/ /\ m.type = MsgProp
       /\ IF leaderId[s] # None
          THEN messages' = messages \cup {[type |-> m.type, from |-> s, to |-> leaderId[s], data |-> m.data]}
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                      matchIndex, nextIndex, votesGranted, pendingConfIndex,
                      uncommittedSize, leadTransferee, isLearner, electionElapsed,
                      heartbeatElapsed, randomizedElectionTimeout>>
    \/ /\ m.type = MsgApp
       /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
       /\ leaderId' = [leaderId EXCEPT ![s] = m.from]
       /\ HandleAppendEntries(s, m)
    \/ /\ m.type = MsgHeartbeat
       /\ electionElapsed' = [electionElapsed EXCEPT ![s] = 0]
       /\ leaderId' = [leaderId EXCEPT ![s] = m.from]
       /\ HandleHeartbeat(s, m)
    \/ /\ m.type = MsgTimeoutNow
       /\ Campaign(s, "Election")

\* Core function: Step - main message processing
Step(s, m) ==
    \/ /\ m.term > currentTerm[s]
       /\ m.type # MsgPreVote
       /\ IF m.type \in {MsgApp, MsgHeartbeat, MsgSnap}
          THEN BecomeFollower(s, m.term, m.from)
          ELSE BecomeFollower(s, m.term, None)
    \/ /\ m.term < currentTerm[s]
       /\ IF m.type \in {MsgHeartbeat, MsgApp}
          THEN messages' = messages \cup {[type |-> MsgAppResp, from |-> s, to |-> m.from, term |-> currentTerm[s]]}
          ELSE IF m.type = MsgPreVote
               THEN messages' = messages \cup {[type |-> MsgPreVoteResp, from |-> s, to |-> m.from, 
                                                term |-> currentTerm[s], reject |-> TRUE]}
               ELSE UNCHANGED messages
       /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                      matchIndex, nextIndex, votesGranted, pendingConfIndex,
                      uncommittedSize, leadTransferee, isLearner, electionElapsed,
                      heartbeatElapsed, randomizedElectionTimeout>>
    \/ /\ m.term = currentTerm[s]
       /\ \/ /\ m.type = MsgHup
             /\ Campaign(s, "Election")
          \/ /\ m.type \in {MsgVote, MsgPreVote}
             /\ HandleVote(s, m)
          \/ /\ state[s] = StateLeader
             /\ StepLeader(s, m)
          \/ /\ state[s] \in {StateCandidate, StatePreCandidate}
             /\ StepCandidate(s, m)
          \/ /\ state[s] = StateFollower
             /\ StepFollower(s, m)






\* Main next state relation
Next == 
    \/ \E s \in Server : 
        /\ electionElapsed[s] >= randomizedElectionTimeout[s]
        /\ state[s] # StateLeader
        /\ Campaign(s, "Election")
    \/ \E s \in Server :
        /\ state[s] = StateLeader
        /\ heartbeatElapsed[s] >= 1
        /\ messages' = messages \cup 
           {[type |-> MsgBeat, from |-> s, to |-> s, term |-> currentTerm[s]]}
        /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = 0]
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                       matchIndex, nextIndex, votesGranted, pendingConfIndex,
                       uncommittedSize, leadTransferee, isLearner, electionElapsed,
                       randomizedElectionTimeout>>
    \/ \E m \in messages, s \in Server :
        /\ m.to = s
        /\ Step(s, m)
        /\ messages' = messages \ {m}
    \/ \E s \in Server :
        /\ electionElapsed' = [electionElapsed EXCEPT ![s] = electionElapsed[s] + 1]
        /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![s] = heartbeatElapsed[s] + 1]
        /\ UNCHANGED <<state, currentTerm, votedFor, log, commitIndex, leaderId,
                       matchIndex, nextIndex, votesGranted, pendingConfIndex,
                       uncommittedSize, leadTransferee, isLearner, randomizedElectionTimeout,
                       messages>>

Spec == Init /\ [][Next]_vars

\* WithoutLeader == \A s \in Server : state[s] /= StateLeader
==== 
