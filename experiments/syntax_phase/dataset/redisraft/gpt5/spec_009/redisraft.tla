---- MODULE redisraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NodeIds,
    ElectionTimeoutMin,
    ElectionTimeoutMax,
    RequestTimeout,
    None

ASSUME ElectionTimeoutMin \in Nat /\ ElectionTimeoutMax \in Nat /\ ElectionTimeoutMin < ElectionTimeoutMax
ASSUME None \notin NodeIds

States == {"FOLLOWER","PRECANDIDATE","CANDIDATE","LEADER"}
EntryType == {"NO_OP","NORMAL","ADD_NODE","ADD_NONVOTING_NODE","REMOVE_NODE"}

Entry == [term: Nat, type: EntryType, node: NodeIds \cup {None}]

IsConfig(e) == e.type \in {"ADD_NODE","ADD_NONVOTING_NODE","REMOVE_NODE"}

ReqVoteMsg(from, to, term, prevote, cand, lli, llt) ==
    [mtype |-> "RequestVote",
     from |-> from, to |-> to, term |-> term, prevote |-> prevote,
     candidate |-> cand, lastIndex |-> lli, lastTerm |-> llt]

ReqVoteResp(from, to, term, prevote, requestTerm, granted) ==
    [mtype |-> "RequestVoteResponse",
     from |-> from, to |-> to, term |-> term, prevote |-> prevote,
     requestTerm |-> requestTerm, voteGranted |-> granted]

AE(from, to, term, leader, pli, plt, ents, lc) ==
    [mtype |-> "AppendEntries",
     from |-> from, to |-> to, term |-> term, leader |-> leader,
     prevLogIndex |-> pli, prevLogTerm |-> plt,
     entries |-> ents, leaderCommit |-> lc]

AEResp(from, to, term, success, curIdx) ==
    [mtype |-> "AppendEntriesResponse",
     from |-> from, to |-> to, term |-> term, success |-> success, currentIndex |-> curIdx]

VARIABLES
    state, currentTerm, votedFor, leaderId,
    log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
    commitIndex, lastApplied,
    Active, Voting,
    HBElapsed, TimeoutElapsed, ETimeoutRand,
    RVotesPre, RVotesReg,
    nextIndex, matchIndex,
    Messages

vars == << state, currentTerm, votedFor, leaderId,
           log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
           commitIndex, lastApplied,
           Active, Voting,
           HBElapsed, TimeoutElapsed, ETimeoutRand,
           RVotesPre, RVotesReg,
           nextIndex, matchIndex,
           Messages >>

Voters == { n \in NodeIds : Active[n] /\ Voting[n] }

Majority(S) == Cardinality(S) >= (Cardinality(Voters) \div 2) + 1

Last(s) == s[Len(s)]

LastIndex(n) == baseIndex[n] + Len(log[n])

LastTerm(n) == IF Len(log[n]) = 0 THEN snapshotLastTerm[n] ELSE (Last(log[n])).term

HasEntryAt(n, idx) == /\ idx > baseIndex[n]
                      /\ idx <= LastIndex(n)

TermAt(n, idx) ==
    IF idx = baseIndex[n] THEN snapshotLastTerm[n]
    ELSE IF HasEntryAt(n, idx) THEN log[n][idx - baseIndex[n]].term
    ELSE 0

PrefixTo(n, idx) ==
    IF idx <= baseIndex[n] THEN <<>>
    ELSE SubSeq(log[n], 1, idx - baseIndex[n])

SuffixFrom(n, idx) ==
    IF idx < baseIndex[n] + 1 THEN log[n]
    ELSE IF idx > LastIndex(n) THEN <<>>
    ELSE SubSeq(log[n], idx - baseIndex[n], Len(log[n]))

UpToDate(cLI, cLT, i) ==
    \/ cLT > LastTerm(i)
    \/ /\ cLT = LastTerm(i)
       /\ cLI >= LastIndex(i)

RandETRange == { k \in Nat : ElectionTimeoutMin <= k /\ k <= ElectionTimeoutMax }

Init ==
    /\ state = [n \in NodeIds |-> "FOLLOWER"]
    /\ currentTerm = [n \in NodeIds |-> 0]
    /\ votedFor = [n \in NodeIds |-> None]
    /\ leaderId = [n \in NodeIds |-> None]
    /\ log = [n \in NodeIds |-> << >>]
    /\ baseIndex = [n \in NodeIds |-> 0]
    /\ snapshotLastTerm = [n \in NodeIds |-> 0]
    /\ snapshotInProgress = [n \in NodeIds |-> FALSE]
    /\ nextSnapshotLastIdx = [n \in NodeIds |-> 0]
    /\ commitIndex = [n \in NodeIds |-> 0]
    /\ lastApplied = [n \in NodeIds |-> 0]
    /\ Active = [n \in NodeIds |-> TRUE]
    /\ Voting = [n \in NodeIds |-> TRUE]
    /\ HBElapsed = [n \in NodeIds |-> 0]
    /\ TimeoutElapsed = [n \in NodeIds |-> 0]
    /\ ETimeoutRand \in [NodeIds -> RandETRange]
    /\ RVotesPre = [n \in NodeIds |-> {}]
    /\ RVotesReg = [n \in NodeIds |-> {}]
    /\ nextIndex = [n \in NodeIds |-> [m \in NodeIds |-> 1]]
    /\ matchIndex = [n \in NodeIds |-> [m \in NodeIds |-> 0]]
    /\ Messages = {}

BecomeFollower(i) ==
    /\ state[i] # "FOLLOWER"
    /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
    /\ leaderId' = [leaderId EXCEPT ![i] = None]
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
    /\ ETimeoutRand' \in [NodeIds -> RandETRange]
    /\ votedFor' = [votedFor EXCEPT ![i] = IF currentTerm[i] # currentTerm[i] THEN None ELSE @]
    /\ RVotesPre' = [RVotesPre EXCEPT ![i] = {}]
    /\ RVotesReg' = [RVotesReg EXCEPT ![i] = {}]
    /\ UNCHANGED << currentTerm, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                    commitIndex, lastApplied, Active, Voting, HBElapsed, nextIndex, matchIndex, Messages >>

BecomePreCandidate(i) ==
    /\ state[i] \in {"FOLLOWER","CANDIDATE"}
    /\ state' = [state EXCEPT ![i] = "PRECANDIDATE"]
    /\ RVotesPre' = [RVotesPre EXCEPT ![i] = {}]
    /\ Messages' =
        Messages \cup
        { ReqVoteMsg(i, j, currentTerm[i] + 1, TRUE, i, LastIndex(i), LastTerm(i))
          : j \in Voters \ {i} }
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED << currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                    commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesReg, nextIndex, matchIndex >>

BecomeCandidate(i) ==
    /\ state[i] \in {"FOLLOWER","PRECANDIDATE"}
    /\ state' = [state EXCEPT ![i] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ RVotesReg' = [RVotesReg EXCEPT ![i] = (IF Voting[i] THEN {i} ELSE {})]
    /\ Messages' =
        Messages \cup
        { ReqVoteMsg(i, j, currentTerm[i] + 1, FALSE, i, LastIndex(i), LastTerm(i))
          : j \in Voters \ {i} }
    /\ leaderId' = [leaderId EXCEPT ![i] = None]
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED << log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                    commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, nextIndex, matchIndex >>

BecomeLeader(i) ==
    /\ state[i] = "CANDIDATE"
    /\ Majority(RVotesReg[i])
    /\ state' = [state EXCEPT ![i] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![i] = i]
    /\ log' = [log EXCEPT ![i] = @ \o << [term |-> currentTerm[i], type |-> "NO_OP", node |-> None] >>]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [m \in NodeIds |-> LastIndex(i) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [m \in NodeIds |-> IF m = i THEN LastIndex(i) + 0 ELSE 0]]
    /\ HBElapsed' = [HBElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED << currentTerm, votedFor, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                    commitIndex, lastApplied, Active, Voting, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, Messages >>

RecvRequestVote ==
    \E m \in Messages:
      /\ m.mtype = "RequestVote"
      /\ LET i == m.to IN
         LET c == m.candidate IN
         /\ Messages' = Messages \ {m}
         /\ IF m.prevote THEN
               /\ IF /\ (leaderId[i] = None \/ TimeoutElapsed[i] >= ETimeoutRand[i] \/ leaderId[i] = c)
                     /\ UpToDate(m.lastIndex, m.lastTerm, i)
                  THEN Messages'' = Messages' \cup { ReqVoteResp(i, m.from, currentTerm[i], TRUE, m.term, TRUE) }
                  ELSE Messages'' = Messages' \cup { ReqVoteResp(i, m.from, currentTerm[i], TRUE, m.term, FALSE) }
               /\ state' = state
               /\ currentTerm' = currentTerm
               /\ votedFor' = votedFor
               /\ leaderId' = leaderId
               /\ TimeoutElapsed' = TimeoutElapsed
            ELSE
               /\ IF m.term > currentTerm[i]
                  THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
                       /\ votedFor' = [votedFor EXCEPT ![i] = None]
                       /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
                  ELSE /\ currentTerm' = currentTerm
                       /\ votedFor' = votedFor
                       /\ state' = state
               /\ IF /\ currentTerm'[i] = m.term
                     /\ (votedFor'[i] = None \/ votedFor'[i] = c)
                     /\ UpToDate(m.lastIndex, m.lastTerm, i)
                  THEN /\ votedFor'' = [votedFor' EXCEPT ![i] = c]
                       /\ Messages'' = Messages' \cup { ReqVoteResp(i, m.from, currentTerm'[i], FALSE, m.term, TRUE) }
                       /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
                       /\ leaderId' = [leaderId EXCEPT ![i] = None]
                  ELSE /\ votedFor'' = votedFor'
                       /\ Messages'' = Messages' \cup { ReqVoteResp(i, m.from, currentTerm'[i], FALSE, m.term, FALSE) }
                       /\ TimeoutElapsed' = TimeoutElapsed
                       /\ leaderId' = leaderId
         /\ Messages' = Messages''
         /\ votedFor' = votedFor''
         /\ UNCHANGED << log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                         commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

RecvRequestVoteResponse ==
    \E m \in Messages:
      /\ m.mtype = "RequestVoteResponse"
      /\ LET i == m.to IN
         /\ Messages' = Messages \ {m}
         /\ IF m.term > currentTerm[i]
            THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
                 /\ votedFor' = [votedFor EXCEPT ![i] = None]
                 /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
                 /\ RVotesPre' = [RVotesPre EXCEPT ![i] = {}]
                 /\ RVotesReg' = [RVotesReg EXCEPT ![i] = {}]
            ELSE
                 /\ currentTerm' = currentTerm
                 /\ votedFor' = votedFor
                 /\ IF m.prevote
                    THEN /\ state[i] = "PRECANDIDATE"
                         /\ m.requestTerm = currentTerm[i] + 1
                         /\ IF m.voteGranted
                            THEN /\ RVotesPre' = [RVotesPre EXCEPT ![i] = @ \cup {m.from}]
                            ELSE /\ RVotesPre' = RVotesPre
                         /\ RVotesReg' = RVotesReg
                         /\ state' = [state EXCEPT ![i] = IF Majority(RVotesPre'[i]) THEN "CANDIDATE" ELSE @]
                         /\ votedFor'' = votedFor'
                         /\ currentTerm'' =
                                IF Majority(RVotesPre'[i]) THEN [currentTerm' EXCEPT ![i] = @ + 1] ELSE currentTerm'
                         /\ votedFor''' =
                                IF Majority(RVotesPre'[i]) THEN [votedFor'' EXCEPT ![i] = i] ELSE votedFor''
                         /\ Messages'' =
                                IF Majority(RVotesPre'[i])
                                THEN Messages' \cup { ReqVoteMsg(i, j, currentTerm[i] + 1, FALSE, i, LastIndex(i), LastTerm(i))
                                                      : j \in Voters \ {i} }
                                ELSE Messages'
                         /\ RVotesReg'' =
                                IF Majority(RVotesPre'[i])
                                THEN [RVotesReg' EXCEPT ![i] = (IF Voting[i] THEN {i} ELSE {})]
                                ELSE RVotesReg'
                         /\ currentTerm' = currentTerm''
                         /\ votedFor' = votedFor'''
                         /\ RVotesReg' = RVotesReg''
                         /\ Messages' = Messages''
                    ELSE /\ state[i] = "CANDIDATE"
                         /\ m.requestTerm = currentTerm[i]
                         /\ IF m.voteGranted
                            THEN /\ RVotesReg' = [RVotesReg EXCEPT ![i] = @ \cup {m.from}]
                            ELSE /\ RVotesReg' = RVotesReg
                         /\ state' = state
                         /\ Messages' = Messages'
         /\ UNCHANGED << leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                         commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, nextIndex, matchIndex >>

SendAppendEntries ==
    \E i \in NodeIds, j \in NodeIds:
      /\ state[i] = "LEADER"
      /\ i # j
      /\ Active[j]
      /\ LET ni == nextIndex[i][j] IN
         /\ ni >= 1
         /\ IF LastIndex(i) >= ni
            THEN /\ ents == SuffixFrom(i, ni)
                 /\ pli == ni - 1
                 /\ plt == TermAt(i, pli)
                 /\ Messages' = Messages \cup { AE(i, j, currentTerm[i], i, pli, plt, ents, commitIndex[i]) }
            ELSE /\ ents == << >>
                 /\ pli == ni - 1
                 /\ plt == TermAt(i, pli)
                 /\ Messages' = Messages \cup { AE(i, j, currentTerm[i], i, pli, plt, << >>, commitIndex[i]) }
         /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                         commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

SendHeartbeat ==
    \E i \in NodeIds:
      /\ state[i] = "LEADER"
      /\ HBElapsed[i] >= RequestTimeout
      /\ Messages' = Messages \cup { AE(i, j, currentTerm[i], i, LastIndex(i), LastTerm(i), << >>, commitIndex[i]) : j \in Active \cap [n \in NodeIds |-> TRUE] \dom Voting /\ Active[j] /\ j # i }
      /\ HBElapsed' = [HBElapsed EXCEPT ![i] = 0]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

RecvAppendEntries ==
    \E m \in Messages:
      /\ m.mtype = "AppendEntries"
      /\ LET i == m.to IN
         /\ Messages' = Messages \ {m} \cup { AEResp(i, m.from, currentTerm[i], TRUE, m.prevLogIndex + Len(m.entries)) }
         /\ IF m.term < currentTerm[i]
            THEN /\ Messages' = (Messages \ {m}) \cup { AEResp(i, m.from, currentTerm[i], FALSE, LastIndex(i)) }
                 /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                                 commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>
            ELSE
              /\ IF m.term > currentTerm[i]
                 THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
                      /\ votedFor' = [votedFor EXCEPT ![i] = None]
                      /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
                 ELSE /\ currentTerm' = currentTerm
                      /\ votedFor' = votedFor
                      /\ state' = state
              /\ leaderId' = [leaderId EXCEPT ![i] = m.leader]
              /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
              /\ IF m.prevLogIndex = baseIndex[i]
                 THEN /\ m.prevLogTerm = snapshotLastTerm[i]
                      /\ okPrev = TRUE
                 ELSE /\ okPrev = HasEntryAt(i, m.prevLogIndex) /\ TermAt(i, m.prevLogIndex) = m.prevLogTerm
              /\ IF ~okPrev
                 THEN /\ Messages' = (Messages \ {m}) \cup { AEResp(i, m.from, currentTerm'[i], FALSE, LastIndex(i)) }
                      /\ UNCHANGED << log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                                      commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>
                 ELSE
                      /\ delFrom == m.prevLogIndex + 1
                      /\ suffix == SuffixFrom(i, delFrom)
                      /\ prefix == PrefixTo(i, delFrom - 1)
                      /\ newLog == prefix \o m.entries
                      /\ log' = [log EXCEPT ![i] = newLog]
                      /\ commitIndex' = [commitIndex EXCEPT ![i] = IF commitIndex[i] < m.leaderCommit THEN Min(m.leaderCommit, LastIndex(i) + Len(m.entries)) ELSE commitIndex[i]]
                      /\ UNCHANGED << snapshotLastTerm, baseIndex, snapshotInProgress, nextSnapshotLastIdx,
                                      lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

LogDelete ==
    \E m \in Messages:
      /\ m.mtype = "AppendEntries"
      /\ LET i == m.to IN
         /\ m.term >= currentTerm[i]
         /\ ( ~HasEntryAt(i, m.prevLogIndex) \/ (HasEntryAt(i, m.prevLogIndex) /\ TermAt(i, m.prevLogIndex) # m.prevLogTerm) )
         /\ Messages' = (Messages \ {m}) \cup { AEResp(i, m.from, currentTerm[i], FALSE, LastIndex(i)) }
         /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                         commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

RecvAppendEntriesResponse ==
    \E m \in Messages:
      /\ m.mtype = "AppendEntriesResponse"
      /\ LET i == m.to IN
         /\ state[i] = "LEADER"
         /\ Messages' = Messages \ {m}
         /\ IF m.term > currentTerm[i]
            THEN /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
                 /\ votedFor' = [votedFor EXCEPT ![i] = None]
                 /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
                 /\ leaderId' = [leaderId EXCEPT ![i] = None]
                 /\ UNCHANGED << log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                                 commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>
            ELSE
              /\ LET f == m.from IN
                 /\ IF m.success
                    THEN /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![f] = Max(@, m.currentIndex)]]
                         /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![f] = Max(@, m.currentIndex + 1)]]
                    ELSE /\ matchIndex' = matchIndex
                         /\ nextIndex' = [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![f] = Max(1, m.currentIndex + 1)]]
                 /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                                 commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg >>

ElectionStart ==
    \E i \in NodeIds:
      /\ state[i] # "LEADER"
      /\ TimeoutElapsed[i] >= ETimeoutRand[i]
      /\ state' = [state EXCEPT ![i] = "PRECANDIDATE"]
      /\ Messages' =
            Messages \cup
            { ReqVoteMsg(i, j, currentTerm[i] + 1, TRUE, i, LastIndex(i), LastTerm(i))
              : j \in Voters \ {i} }
      /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
      /\ RVotesPre' = [RVotesPre EXCEPT ![i] = {}]
      /\ UNCHANGED << currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesReg, nextIndex, matchIndex >>

ElectionTimeout ==
    \E i \in NodeIds:
      /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = @ + 1]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

PeriodicElectionTimeout ==
    \E i \in NodeIds:
      /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = @ + 1]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

PeriodicHeartbeat ==
    \E i \in NodeIds:
      /\ state[i] = "LEADER"
      /\ HBElapsed' = [HBElapsed EXCEPT ![i] = @ + 1]
      /\ IF HBElapsed'[i] >= RequestTimeout
         THEN /\ Messages' = Messages \cup { AE(i, j, currentTerm[i], i, LastIndex(i), LastTerm(i), << >>, commitIndex[i]) : j \in Voters \ {i} }
              /\ HBElapsed' = [HBElapsed EXCEPT ![i] = 0]
         ELSE /\ Messages' = Messages
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

LogAppend ==
    \E i \in NodeIds, e \in Entry:
      /\ state[i] = "LEADER"
      /\ e.term = currentTerm[i]
      /\ log' = [log EXCEPT ![i] = @ \o << e >>]
      /\ matchIndex' = [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![i] = LastIndex(i) + 1]]
      /\ nextIndex' = nextIndex
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, Messages >>

LogCommit ==
    \E i \in NodeIds:
      /\ state[i] = "LEADER"
      /\ LET S == { k \in Nat :
                     /\ commitIndex[i] < k
                     /\ k <= LastIndex(i)
                     /\ Cardinality({ n \in Voters : (IF n = i THEN LastIndex(i) ELSE matchIndex[i][n]) >= k }) >= (Cardinality(Voters) \div 2) + 1
                     /\ TermAt(i, k) = currentTerm[i]
                   } IN
         /\ commitIndex' = [commitIndex EXCEPT ![i] = IF S = {} THEN @ ELSE CHOOSE k \in S : \A j \in S : j <= k]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

AddNode ==
    \E i \in NodeIds, nid \in NodeIds:
      /\ state[i] = "LEADER"
      /\ ~Active[nid]
      /\ let e == [term |-> currentTerm[i], type |-> "ADD_NODE", node |-> nid] in
         /\ log' = [log EXCEPT ![i] = @ \o << e >>]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

RemoveNode ==
    \E i \in NodeIds, nid \in NodeIds:
      /\ state[i] = "LEADER"
      /\ Active[nid]
      /\ let e == [term |-> currentTerm[i], type |-> "REMOVE_NODE", node |-> nid] in
         /\ log' = [log EXCEPT ![i] = @ \o << e >>]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

ApplyConfigChange ==
    \E i \in NodeIds:
      /\ lastApplied[i] < commitIndex[i]
      /\ HasEntryAt(i, lastApplied[i] + 1)
      /\ IsConfig(log[i][lastApplied[i] + 1 - baseIndex[i]])
      /\ LET e == log[i][lastApplied[i] + 1 - baseIndex[i]] IN
         /\ lastApplied' = [lastApplied EXCEPT ![i] = @ + 1]
         /\ IF e.type = "ADD_NODE"
            THEN /\ Active' = [Active EXCEPT ![e.node] = TRUE]
                 /\ Voting' = [Voting EXCEPT ![e.node] = TRUE]
            ELSE IF e.type = "ADD_NONVOTING_NODE"
                 THEN /\ Active' = [Active EXCEPT ![e.node] = TRUE]
                      /\ Voting' = [Voting EXCEPT ![e.node] = FALSE]
                 ELSE /\ e.type = "REMOVE_NODE"
                      /\ Active' = [Active EXCEPT ![e.node] = FALSE]
                      /\ Voting' = Voting
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

ApplyNormal ==
    \E i \in NodeIds:
      /\ lastApplied[i] < commitIndex[i]
      /\ HasEntryAt(i, lastApplied[i] + 1)
      /\ ~IsConfig(log[i][lastApplied[i] + 1 - baseIndex[i]])
      /\ lastApplied' = [lastApplied EXCEPT ![i] = @ + 1]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

SnapshotBegin ==
    \E i \in NodeIds:
      /\ ~snapshotInProgress[i]
      /\ lastApplied[i] > baseIndex[i]
      /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![i] = TRUE]
      /\ nextSnapshotLastIdx' = [nextSnapshotLastIdx EXCEPT ![i] = lastApplied[i]]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm,
                      commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

SnapshotEnd ==
    \E i \in NodeIds:
      /\ snapshotInProgress[i]
      /\ nextSnapshotLastIdx[i] >= baseIndex[i]
      /\ let k == nextSnapshotLastIdx[i] - baseIndex[i] in
         /\ snapshotLastTerm' = [snapshotLastTerm EXCEPT ![i] = TermAt(i, nextSnapshotLastIdx[i])]
         /\ baseIndex' = [baseIndex EXCEPT ![i] = nextSnapshotLastIdx[i]]
         /\ log' = [log EXCEPT ![i] = SubSeq(log[i], k + 1, Len(log[i]))]
         /\ snapshotInProgress' = [snapshotInProgress EXCEPT ![i] = FALSE]
         /\ nextSnapshotLastIdx' = [nextSnapshotLastIdx EXCEPT ![i] = 0]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId,
                      commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

PeriodicTick ==
    \E i \in NodeIds:
      /\ HBElapsed' = [HBElapsed EXCEPT ![i] = @ + 1]
      /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = @ + 1]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

Next ==
    \/ BecomeFollower(\E n \in NodeIds : n)
    \/ BecomePreCandidate(\E n \in NodeIds : n)
    \/ BecomeCandidate(\E n \in NodeIds : n)
    \/ BecomeLeader(\E n \in NodeIds : n)
    \/ RecvRequestVote
    \/ RecvRequestVoteResponse
    \/ RecvAppendEntries
    \/ RecvAppendEntriesResponse
    \/ SendAppendEntries
    \/ SendHeartbeat
    \/ ElectionStart
    \/ ElectionTimeout
    \/ LogAppend
    \/ LogDelete
    \/ LogCommit
    \/ PeriodicElectionTimeout
    \/ PeriodicHeartbeat
    \/ AddNode
    \/ RemoveNode
    \/ SnapshotBegin
    \/ SnapshotEnd
    \/ ApplyConfigChange
    \/ ApplyNormal
    \/ PeriodicTick
    \/ UNCHANGED vars

====