---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS
    NodeIds,
    ElectionTimeoutMin,
    ElectionTimeoutMax,
    RequestTimeout,
    None

ASSUME ElectionTimeoutMin \in Nat /\ ElectionTimeoutMax \in Nat /\ ElectionTimeoutMin < ElectionTimeoutMax
ASSUME None \notin NodeIds
ASSUME RequestTimeout \in Nat

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

HasEntryAt(n, idx) ==
    /\ idx > baseIndex[n]
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
    /\ i \in NodeIds
    /\ state[i] # "FOLLOWER"
    /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
    /\ leaderId' = [leaderId EXCEPT ![i] = None]
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
    /\ RVotesPre' = [RVotesPre EXCEPT ![i] = {}]
    /\ RVotesReg' = [RVotesReg EXCEPT ![i] = {}]
    /\ UNCHANGED << currentTerm, votedFor, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                    commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, nextIndex, matchIndex, Messages >>

BecomePreCandidate(i) ==
    /\ i \in NodeIds
    /\ state[i] \in {"FOLLOWER","CANDIDATE"}
    /\ state' = [state EXCEPT ![i] = "PRECANDIDATE"]
    /\ RVotesPre' = [RVotesPre EXCEPT ![i] = {}]
    /\ Messages' = Messages \cup { ReqVoteMsg(i, j, currentTerm[i] + 1, TRUE, i, LastIndex(i), LastTerm(i)) : j \in (Voters \ {i}) }
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED << currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                    commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesReg, nextIndex, matchIndex >>

BecomeCandidate(i) ==
    /\ i \in NodeIds
    /\ state[i] \in {"FOLLOWER","PRECANDIDATE"}
    /\ state' = [state EXCEPT ![i] = "CANDIDATE"]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = @ + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ RVotesReg' = [RVotesReg EXCEPT ![i] = IF Voting[i] THEN {i} ELSE {}]
    /\ Messages' = Messages \cup { ReqVoteMsg(i, j, currentTerm[i] + 1, FALSE, i, LastIndex(i), LastTerm(i)) : j \in (Voters \ {i}) }
    /\ leaderId' = [leaderId EXCEPT ![i] = None]
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED << log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                    commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, nextIndex, matchIndex >>

BecomeLeader(i) ==
    /\ i \in NodeIds
    /\ state[i] = "CANDIDATE"
    /\ Majority(RVotesReg[i])
    /\ state' = [state EXCEPT ![i] = "LEADER"]
    /\ leaderId' = [leaderId EXCEPT ![i] = i]
    /\ log' = [log EXCEPT ![i] = @ \o << [term |-> currentTerm[i], type |-> "NO_OP", node |-> None] >>]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [m \in NodeIds |-> LastIndex(i) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [m \in NodeIds |-> IF m = i THEN LastIndex(i) ELSE 0]]
    /\ HBElapsed' = [HBElapsed EXCEPT ![i] = 0]
    /\ UNCHANGED << currentTerm, votedFor, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                    commitIndex, lastApplied, Active, Voting, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, Messages >>

RecvRequestVote ==
    \E m \in Messages:
      /\ m.mtype = "RequestVote"
      /\ LET i == m.to IN
         LET M0 == Messages \ {m} IN
         IF m.prevote
         THEN
           LET grant == ((leaderId[i] = None) \/ (TimeoutElapsed[i] >= ETimeoutRand[i]) \/ (leaderId[i] = m.candidate))
                         /\ UpToDate(m.lastIndex, m.lastTerm, i) IN
           /\ Messages' = M0 \cup { ReqVoteResp(i, m.from, currentTerm[i], TRUE, m.term, grant) }
           /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                           commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>
         ELSE
           LET ct1 == IF m.term > currentTerm[i] THEN [currentTerm EXCEPT ![i] = m.term] ELSE currentTerm IN
           LET vf1 == IF m.term > currentTerm[i] THEN [votedFor EXCEPT ![i] = None] ELSE votedFor IN
           LET st1 == IF m.term > currentTerm[i] THEN [state EXCEPT ![i] = "FOLLOWER"] ELSE state IN
           LET grant == (ct1[i] = m.term) /\ (vf1[i] = None \/ vf1[i] = m.candidate) /\ UpToDate(m.lastIndex, m.lastTerm, i) IN
           LET vf2 == IF grant THEN [vf1 EXCEPT ![i] = m.candidate] ELSE vf1 IN
           LET to2 == IF grant THEN [TimeoutElapsed EXCEPT ![i] = 0] ELSE TimeoutElapsed IN
           LET ld2 == IF grant THEN [leaderId EXCEPT ![i] = None] ELSE leaderId IN
           /\ state' = st1
           /\ currentTerm' = ct1
           /\ votedFor' = vf2
           /\ leaderId' = ld2
           /\ TimeoutElapsed' = to2
           /\ Messages' = M0 \cup { ReqVoteResp(i, m.from, ct1[i], FALSE, m.term, grant) }
           /\ UNCHANGED << log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                           commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

RecvRequestVoteResponse ==
    \E m \in Messages:
      /\ m.mtype = "RequestVoteResponse"
      /\ LET i == m.to IN
         LET M0 == Messages \ {m} IN
         IF m.term > currentTerm[i]
         THEN
           /\ Messages' = M0
           /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
           /\ votedFor' = [votedFor EXCEPT ![i] = None]
           /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
           /\ RVotesPre' = [RVotesPre EXCEPT ![i] = {}]
           /\ RVotesReg' = [RVotesReg EXCEPT ![i] = {}]
           /\ leaderId' = [leaderId EXCEPT ![i] = None]
           /\ UNCHANGED << log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                           commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, nextIndex, matchIndex >>
         ELSE
           IF m.prevote /\ state[i] = "PRECANDIDATE" /\ m.requestTerm = currentTerm[i] + 1
           THEN
             LET rvp1 == IF m.voteGranted THEN [RVotesPre EXCEPT ![i] = @ \cup {m.from}] ELSE RVotesPre IN
             LET become == Majority(rvp1[i]) IN
             LET st2 == IF become THEN [state EXCEPT ![i] = "CANDIDATE"] ELSE state IN
             LET ct2 == IF become THEN [currentTerm EXCEPT ![i] = @ + 1] ELSE currentTerm IN
             LET vf2 == IF become THEN [votedFor EXCEPT ![i] = i] ELSE votedFor IN
             LET rvr2 == IF become THEN [RVotesReg EXCEPT ![i] = IF Voting[i] THEN {i} ELSE {}] ELSE RVotesReg IN
             LET msgs2 == IF become
                          THEN M0 \cup { ReqVoteMsg(i, j, currentTerm[i] + 1, FALSE, i, LastIndex(i), LastTerm(i)) : j \in (Voters \ {i}) }
                          ELSE M0 IN
             /\ state' = st2
             /\ currentTerm' = ct2
             /\ votedFor' = vf2
             /\ RVotesPre' = rvp1
             /\ RVotesReg' = rvr2
             /\ Messages' = msgs2
             /\ UNCHANGED << leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                             commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, nextIndex, matchIndex >>
           ELSE
             IF ~m.prevote /\ state[i] = "CANDIDATE" /\ m.requestTerm = currentTerm[i]
             THEN
               LET rvr1 == IF m.voteGranted THEN [RVotesReg EXCEPT ![i] = @ \cup {m.from}] ELSE RVotesReg IN
               /\ RVotesReg' = rvr1
               /\ Messages' = M0
               /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                               commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, nextIndex, matchIndex >>
             ELSE
               /\ Messages' = M0
               /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                               commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

SendAppendEntries ==
    \E i \in NodeIds, j \in NodeIds:
      /\ state[i] = "LEADER"
      /\ i # j
      /\ Active[j]
      /\ LET ni == nextIndex[i][j] IN
         LET pli == ni - 1 IN
         LET plt == TermAt(i, pli) IN
         LET ents == (IF LastIndex(i) >= ni THEN SuffixFrom(i, ni) ELSE << >>) IN
         /\ Messages' = Messages \cup { AE(i, j, currentTerm[i], i, pli, plt, ents, commitIndex[i]) }
         /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                         commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

PeriodicHeartbeat ==
    \E i \in NodeIds:
      /\ state[i] = "LEADER"
      /\ LET hb1 == HBElapsed[i] + 1 IN
         LET send == hb1 >= RequestTimeout IN
         LET recips == { j \in NodeIds : Active[j] /\ j # i } IN
         /\ HBElapsed' = [HBElapsed EXCEPT ![i] = IF send THEN 0 ELSE hb1]
         /\ Messages' =
              IF send
              THEN Messages \cup { AE(i, j, currentTerm[i], i, LastIndex(i), LastTerm(i), << >>, commitIndex[i]) : j \in recips }
              ELSE Messages
         /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                         commitIndex, lastApplied, Active, Voting, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

RecvAppendEntries ==
    \E m \in Messages:
      /\ m.mtype = "AppendEntries"
      /\ LET i == m.to IN
         LET M0 == Messages \ {m} IN
         IF m.term < currentTerm[i]
         THEN
           /\ Messages' = M0 \cup { AEResp(i, m.from, currentTerm[i], FALSE, LastIndex(i)) }
           /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                           commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>
         ELSE
           LET ct1 == IF m.term > currentTerm[i] THEN [currentTerm EXCEPT ![i] = m.term] ELSE currentTerm IN
           LET vf1 == IF m.term > currentTerm[i] THEN [votedFor EXCEPT ![i] = None] ELSE votedFor IN
           LET st1 == IF m.term > currentTerm[i] THEN [state EXCEPT ![i] = "FOLLOWER"] ELSE state IN
           LET okPrev ==
                IF m.prevLogIndex = baseIndex[i]
                THEN m.prevLogTerm = snapshotLastTerm[i]
                ELSE (HasEntryAt(i, m.prevLogIndex) /\ TermAt(i, m.prevLogIndex) = m.prevLogTerm)
           IN
           IF ~okPrev
           THEN
             /\ state' = st1
             /\ currentTerm' = ct1
             /\ votedFor' = vf1
             /\ leaderId' = [leaderId EXCEPT ![i] = m.leader]
             /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
             /\ Messages' = M0 \cup { AEResp(i, m.from, ct1[i], FALSE, LastIndex(i)) }
             /\ UNCHANGED << log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                             commitIndex, lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>
           ELSE
             LET delFrom == m.prevLogIndex + 1 IN
             LET prefix == PrefixTo(i, delFrom - 1) IN
             LET newLogI == prefix \o m.entries IN
             LET log2 == [log EXCEPT ![i] = newLogI] IN
             LET newLastI == baseIndex[i] + Len(newLogI) IN
             LET commit2 == [commitIndex EXCEPT ![i] = IF commitIndex[i] < m.leaderCommit THEN Min(m.leaderCommit, newLastI) ELSE commitIndex[i]] IN
             /\ state' = st1
             /\ currentTerm' = ct1
             /\ votedFor' = vf1
             /\ leaderId' = [leaderId EXCEPT ![i] = m.leader]
             /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![i] = 0]
             /\ log' = log2
             /\ commitIndex' = commit2
             /\ Messages' = M0 \cup { AEResp(i, m.from, ct1[i], TRUE, m.prevLogIndex + Len(m.entries)) }
             /\ UNCHANGED << baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                             lastApplied, Active, Voting, HBElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

RecvAppendEntriesResponse ==
    \E m \in Messages:
      /\ m.mtype = "AppendEntriesResponse"
      /\ LET i == m.to IN
         LET M0 == Messages \ {m} IN
         IF m.term > currentTerm[i]
         THEN
           /\ Messages' = M0
           /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
           /\ votedFor' = [votedFor EXCEPT ![i] = None]
           /\ state' = [state EXCEPT ![i] = "FOLLOWER"]
           /\ leaderId' = [leaderId EXCEPT ![i] = None]
           /\ UNCHANGED << log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                           commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>
         ELSE
           IF state[i] = "LEADER"
           THEN
             LET f == m.from IN
             LET mi2 == IF m.success
                        THEN [matchIndex EXCEPT ![i] = [matchIndex[i] EXCEPT ![f] = Max(@, m.currentIndex)]]
                        ELSE matchIndex IN
             LET ni2 == IF m.success
                        THEN [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![f] = Max(@, m.currentIndex + 1)]]
                        ELSE [nextIndex EXCEPT ![i] = [nextIndex[i] EXCEPT ![f] = Max(1, m.currentIndex + 1)]] IN
             /\ matchIndex' = mi2
             /\ nextIndex' = ni2
             /\ Messages' = M0
             /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                             commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg >>
           ELSE
             /\ Messages' = M0
             /\ UNCHANGED << state, currentTerm, votedFor, leaderId, log, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                             commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex >>

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
      /\ LET e == [term |-> currentTerm[i], type |-> "ADD_NODE", node |-> nid] IN
         /\ log' = [log EXCEPT ![i] = @ \o << e >>]
      /\ UNCHANGED << state, currentTerm, votedFor, leaderId, baseIndex, snapshotLastTerm, snapshotInProgress, nextSnapshotLastIdx,
                      commitIndex, lastApplied, Active, Voting, HBElapsed, TimeoutElapsed, ETimeoutRand, RVotesPre, RVotesReg, nextIndex, matchIndex, Messages >>

RemoveNode ==
    \E i \in NodeIds, nid \in NodeIds:
      /\ state[i] = "LEADER"
      /\ Active[nid]
      /\ LET e == [term |-> currentTerm[i], type |-> "REMOVE_NODE", node |-> nid] IN
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
      /\ LET k == nextSnapshotLastIdx[i] - baseIndex[i] IN
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
    \/ \E i \in NodeIds : BecomeFollower(i)
    \/ \E i \in NodeIds : BecomePreCandidate(i)
    \/ \E i \in NodeIds : BecomeCandidate(i)
    \/ \E i \in NodeIds : BecomeLeader(i)
    \/ RecvRequestVote
    \/ RecvRequestVoteResponse
    \/ RecvAppendEntries
    \/ RecvAppendEntriesResponse
    \/ SendAppendEntries
    \/ PeriodicHeartbeat
    \/ LogAppend
    \/ LogCommit
    \/ AddNode
    \/ RemoveNode
    \/ SnapshotBegin
    \/ SnapshotEnd
    \/ ApplyConfigChange
    \/ ApplyNormal
    \/ PeriodicTick
    \/ UNCHANGED vars

====