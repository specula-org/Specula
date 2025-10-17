---- MODULE redisraft ----
EXTENDS TLC, Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,
    None,
    ELECTION_TIMEOUT,
    REQUEST_TIMEOUT,
    SNAPSHOT_THRESHOLD

ASSUME None \notin Nodes

VARIABLES
    State,
    CurrentTerm,
    VotedFor,
    LeaderId,
    TimeoutElapsed,
    ETimeoutRand,
    HBElapsed,
    MsgId,
    Log,
    CommitIndex,
    LastApplied,
    SnapshotLastIndex,
    SnapshotLastTerm,
    SnapshotInProgress,
    NextSnapIndex,
    NextSnapTerm,
    NextIndex,
    MatchIndex,
    Net,
    Members,
    Voting,
    VotesGranted,
    PreVotesGranted

States == {"FOLLOWER","PRECANDIDATE","CANDIDATE","LEADER"}

EntryTypes == {"data","noop","add_node","add_nonvoting_node","remove_node"}

Entry(e) == /\ e \in [term: Nat, etype: EntryTypes, node: (Nodes \cup {None})]

Base(n) == SnapshotLastIndex[n]
BaseTerm(n) == SnapshotLastTerm[n]
LenLog(n) == Len(Log[n])
LastIndex(n) == Base(n) + LenLog(n)
HasEntryAt(n, idx) == /\ idx > Base(n) /\ idx <= LastIndex(n)
Pos(n, idx) == idx - Base(n)
TermAt(n, idx) ==
    IF idx = Base(n) THEN BaseTerm(n)
    ELSE IF HasEntryAt(n, idx) THEN Log[n][Pos(n, idx)].term
    ELSE 0
EntryAt(n, idx) == Log[n][Pos(n, idx)]
EntriesFrom(n, idx) ==
    IF idx > LastIndex(n) THEN <<>>
    ELSE SubSeq(Log[n], Pos(n, idx), LenLog(n))

AppendSeq(s, t) == IF Len(t) = 0 THEN s ELSE s \o t

MajoritySize(S) == (Cardinality(S) \div 2) + 1

IsAEReq(m) == /\ m.type = "AppendEntriesReq" /\ m \in Net
IsAEResp(m) == /\ m.type = "AppendEntriesResp" /\ m \in Net
IsRVReq(m) == /\ m.type = "RequestVoteReq" /\ m \in Net
IsRVResp(m) == /\ m.type = "RequestVoteResp" /\ m \in Net

UpToDate(cLastIdx, cLastTerm, sLastIdx, sLastTerm) ==
    \/ cLastTerm > sLastTerm
    \/ /\ cLastTerm = sLastTerm
       /\ cLastIdx >= sLastIdx

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b
Min(S) == CHOOSE x \in S: \A y \in S: x <= y

RandomizeTimeout(n) ==
    \E v \in ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT):
      ETimeoutRand' = [ETimeoutRand EXCEPT ![n] = v]

Init ==
    /\ State \in [Nodes -> States]
    /\ \A n \in Nodes: State[n] = "FOLLOWER"
    /\ CurrentTerm \in [Nodes -> Nat]
    /\ \A n \in Nodes: CurrentTerm[n] = 0
    /\ VotedFor \in [Nodes -> (Nodes \cup {None})]
    /\ \A n \in Nodes: VotedFor[n] = None
    /\ LeaderId \in [Nodes -> (Nodes \cup {None})]
    /\ \A n \in Nodes: LeaderId[n] = None
    /\ TimeoutElapsed \in [Nodes -> Nat]
    /\ \A n \in Nodes: TimeoutElapsed[n] = 0
    /\ ETimeoutRand \in [Nodes -> Nat]
    /\ \A n \in Nodes: ETimeoutRand[n] \in ELECTION_TIMEOUT..(2 * ELECTION_TIMEOUT)
    /\ HBElapsed \in [Nodes -> Nat]
    /\ \A n \in Nodes: HBElapsed[n] = 0
    /\ MsgId \in [Nodes -> Nat]
    /\ \A n \in Nodes: MsgId[n] = 0
    /\ Log \in [Nodes -> Seq([term: Nat, etype: EntryTypes, node: (Nodes \cup {None})])]
    /\ \A n \in Nodes: Log[n] = <<>>
    /\ CommitIndex \in [Nodes -> Nat]
    /\ \A n \in Nodes: CommitIndex[n] = 0
    /\ LastApplied \in [Nodes -> Nat]
    /\ \A n \in Nodes: LastApplied[n] = 0
    /\ SnapshotLastIndex \in [Nodes -> Nat]
    /\ \A n \in Nodes: SnapshotLastIndex[n] = 0
    /\ SnapshotLastTerm \in [Nodes -> Nat]
    /\ \A n \in Nodes: SnapshotLastTerm[n] = 0
    /\ SnapshotInProgress \in [Nodes -> BOOLEAN]
    /\ \A n \in Nodes: SnapshotInProgress[n] = FALSE
    /\ NextSnapIndex \in [Nodes -> Nat]
    /\ \A n \in Nodes: NextSnapIndex[n] = 0
    /\ NextSnapTerm \in [Nodes -> Nat]
    /\ \A n \in Nodes: NextSnapTerm[n] = 0
    /\ NextIndex \in [Nodes -> [Nodes -> Nat]]
    /\ \A n \in Nodes: \A m \in Nodes: NextIndex[n][m] = 1
    /\ MatchIndex \in [Nodes -> [Nodes -> Nat]]
    /\ \A n \in Nodes: \A m \in Nodes: MatchIndex[n][m] = 0
    /\ Net = {}
    /\ Members \subseteq Nodes
    /\ Members = Nodes
    /\ Voting \subseteq Members
    /\ Voting = Members
    /\ VotesGranted \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes: VotesGranted[n] = {}
    /\ PreVotesGranted \in [Nodes -> SUBSET Nodes]
    /\ \A n \in Nodes: PreVotesGranted[n] = {}

BecomeFollower(n) ==
    /\ State[n] # "FOLLOWER"
    /\ State' = [State EXCEPT ![n] = "FOLLOWER"]
    /\ LeaderId' = [LeaderId EXCEPT ![n] = None]
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![n] = 0]
    /\ VotedFor' = [VotedFor EXCEPT ![n] = None]
    /\ CurrentTerm' = CurrentTerm
    /\ HBElapsed' = HBElapsed
    /\ MsgId' = MsgId
    /\ Log' = Log
    /\ CommitIndex' = CommitIndex
    /\ LastApplied' = LastApplied
    /\ SnapshotLastIndex' = SnapshotLastIndex
    /\ SnapshotLastTerm' = SnapshotLastTerm
    /\ SnapshotInProgress' = SnapshotInProgress
    /\ NextSnapIndex' = NextSnapIndex
    /\ NextSnapTerm' = NextSnapTerm
    /\ NextIndex' = NextIndex
    /\ MatchIndex' = MatchIndex
    /\ Members' = Members
    /\ Voting' = Voting
    /\ VotesGranted' = VotesGranted
    /\ PreVotesGranted' = PreVotesGranted
    /\ Net' = Net
    /\ RandomizeTimeout(n)

BecomePreCandidate(n) ==
    /\ n \in Voting
    /\ State[n] # "LEADER"
    /\ State' = [State EXCEPT ![n] = "PRECANDIDATE"]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {}]
    /\ Net' =
        Net \cup { [type |-> "RequestVoteReq",
                    from |-> n, to |-> m,
                    term |-> CurrentTerm[n] + 1,
                    prevote |-> TRUE,
                    lastLogIndex |-> LastIndex(n),
                    lastLogTerm |-> TermAt(n, LastIndex(n)),
                    candidate |-> n] : m \in Voting \ {n} }
    /\ LeaderId' = LeaderId
    /\ VotedFor' = VotedFor
    /\ CurrentTerm' = CurrentTerm
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![n] = 0]
    /\ HBElapsed' = HBElapsed
    /\ MsgId' = MsgId
    /\ Log' = Log
    /\ CommitIndex' = CommitIndex
    /\ LastApplied' = LastApplied
    /\ SnapshotLastIndex' = SnapshotLastIndex
    /\ SnapshotLastTerm' = SnapshotLastTerm
    /\ SnapshotInProgress' = SnapshotInProgress
    /\ NextSnapIndex' = NextSnapIndex
    /\ NextSnapTerm' = NextSnapTerm
    /\ NextIndex' = NextIndex
    /\ MatchIndex' = MatchIndex
    /\ Members' = Members
    /\ Voting' = Voting
    /\ ETimeoutRand' = ETimeoutRand

BecomeCandidate(n) ==
    /\ n \in Voting
    /\ State[n] \in {"PRECANDIDATE","FOLLOWER","CANDIDATE"}
    /\ State' = [State EXCEPT ![n] = "CANDIDATE"]
    /\ CurrentTerm' = [CurrentTerm EXCEPT ![n] = CurrentTerm[n] + 1]
    /\ VotedFor' = [VotedFor EXCEPT ![n] = n]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {n}]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ Net' =
        Net \cup { [type |-> "RequestVoteReq",
                    from |-> n, to |-> m,
                    term |-> CurrentTerm[n] + 1,
                    prevote |-> FALSE,
                    lastLogIndex |-> LastIndex(n),
                    lastLogTerm |-> TermAt(n, LastIndex(n)),
                    candidate |-> n] : m \in Voting \ {n} }
    /\ LeaderId' = [LeaderId EXCEPT ![n] = None]
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![n] = 0]
    /\ HBElapsed' = HBElapsed
    /\ MsgId' = MsgId
    /\ Log' = Log
    /\ CommitIndex' = CommitIndex
    /\ LastApplied' = LastApplied
    /\ SnapshotLastIndex' = SnapshotLastIndex
    /\ SnapshotLastTerm' = SnapshotLastTerm
    /\ SnapshotInProgress' = SnapshotInProgress
    /\ NextSnapIndex' = NextSnapIndex
    /\ NextSnapTerm' = NextSnapTerm
    /\ NextIndex' = NextIndex
    /\ MatchIndex' = MatchIndex
    /\ Members' = Members
    /\ Voting' = Voting
    /\ RandomizeTimeout(n)

BecomeLeader(n) ==
    /\ State[n] = "CANDIDATE"
    /\ VotesGranted[n] \subseteq Voting
    /\ Cardinality(VotesGranted[n]) >= MajoritySize(Voting)
    /\ LET prevIdx == LastIndex(n) IN
       LET prevTerm == TermAt(n, prevIdx) IN
       LET noop == [term |-> CurrentTerm[n], etype |-> "noop", node |-> None] IN
       LET logN == Log[n] \o << noop >> IN
       /\ State' = [State EXCEPT ![n] = "LEADER"]
       /\ LeaderId' = [LeaderId EXCEPT ![n] = n]
       /\ MsgId' = [MsgId EXCEPT ![n] = MsgId[n] + 1]
       /\ Log' = [Log EXCEPT ![n] = logN]
       /\ NextIndex' = [NextIndex EXCEPT ![n] = [m \in Nodes |-> (prevIdx + 2)]]
       /\ MatchIndex' = [MatchIndex EXCEPT ![n] = [m \in Nodes |-> IF m = n THEN prevIdx + 1 ELSE 0]]
       /\ Net' =
            Net \cup { [type |-> "AppendEntriesReq",
                        from |-> n, to |-> m,
                        term |-> CurrentTerm[n],
                        prevLogIndex |-> prevIdx,
                        prevLogTerm |-> prevTerm,
                        entries |-> << noop >>,
                        leaderCommit |-> CommitIndex[n],
                        msgId |-> MsgId[n] + 1] : m \in Members \ {n} }
       /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![n] = 0]
       /\ HBElapsed' = [HBElapsed EXCEPT ![n] = 0]
       /\ CommitIndex' = CommitIndex
       /\ LastApplied' = LastApplied
       /\ SnapshotLastIndex' = SnapshotLastIndex
       /\ SnapshotLastTerm' = SnapshotLastTerm
       /\ SnapshotInProgress' = SnapshotInProgress
       /\ NextSnapIndex' = NextSnapIndex
       /\ NextSnapTerm' = NextSnapTerm
       /\ Members' = Members
       /\ Voting' = Voting
       /\ VotesGranted' = VotesGranted
       /\ PreVotesGranted' = PreVotesGranted
       /\ RandomizeTimeout(n)

ElectionStart(n) ==
    /\ n \in Voting
    /\ State[n] # "LEADER"
    /\ State' = [State EXCEPT ![n] = "PRECANDIDATE"]
    /\ LeaderId' = [LeaderId EXCEPT ![n] = None]
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![n] = 0]
    /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![n] = {}]
    /\ VotesGranted' = [VotesGranted EXCEPT ![n] = {}]
    /\ Net' =
        Net \cup { [type |-> "RequestVoteReq",
                    from |-> n, to |-> m,
                    term |-> CurrentTerm[n] + 1,
                    prevote |-> TRUE,
                    lastLogIndex |-> LastIndex(n),
                    lastLogTerm |-> TermAt(n, LastIndex(n)),
                    candidate |-> n] : m \in Voting \ {n} }
    /\ VotedFor' = VotedFor
    /\ CurrentTerm' = CurrentTerm
    /\ HBElapsed' = HBElapsed
    /\ MsgId' = MsgId
    /\ Log' = Log
    /\ CommitIndex' = CommitIndex
    /\ LastApplied' = LastApplied
    /\ SnapshotLastIndex' = SnapshotLastIndex
    /\ SnapshotLastTerm' = SnapshotLastTerm
    /\ SnapshotInProgress' = SnapshotInProgress
    /\ NextSnapIndex' = NextSnapIndex
    /\ NextSnapTerm' = NextSnapTerm
    /\ NextIndex' = NextIndex
    /\ MatchIndex' = MatchIndex
    /\ Members' = Members
    /\ Voting' = Voting
    /\ RandomizeTimeout(n)

ElectionTimeout(n) ==
    /\ State[n] # "LEADER"
    /\ TimeoutElapsed[n] >= ETimeoutRand[n]
    /\ ElectionStart(n)

PeriodicElectionTimeout(n) ==
    /\ State[n] # "LEADER"
    /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![n] = TimeoutElapsed[n] + 1]
    /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

PeriodicHeartbeat(n) ==
    /\ State[n] = "LEADER"
    /\ HBElapsed' = [HBElapsed EXCEPT ![n] = HBElapsed[n] + 1]
    /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

SendHeartbeat(n) ==
    /\ State[n] = "LEADER"
    /\ HBElapsed[n] >= REQUEST_TIMEOUT
    /\ Net' =
        Net \cup { [type |-> "AppendEntriesReq",
                    from |-> n, to |-> m,
                    term |-> CurrentTerm[n],
                    prevLogIndex |-> NextIndex[n][m] - 1,
                    prevLogTerm |-> TermAt(n, NextIndex[n][m] - 1),
                    entries |-> <<>>,
                    leaderCommit |-> CommitIndex[n],
                    msgId |-> MsgId[n] + 1] : m \in Members \ {n} }
    /\ MsgId' = [MsgId EXCEPT ![n] = MsgId[n] + 1]
    /\ HBElapsed' = [HBElapsed EXCEPT ![n] = 0]
    /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Members, Voting, VotesGranted, PreVotesGranted >>

SendAppendEntries(n, m) ==
    /\ State[n] = "LEADER"
    /\ m \in Members \ {n}
    /\ NextIndex[n][m] >= Base(n) + 1
    /\ NextIndex[n][m] <= LastIndex(n) + 1
    /\ \E k \in Nat:
        /\ k >= 1
        /\ NextIndex[n][m] + k - 1 <= LastIndex(n)
        /\ LET pos == Pos(n, NextIndex[n][m]) IN
           LET ents == SubSeq(Log[n], pos, pos + k - 1) IN
               /\ Net' =
                    Net \cup { [type |-> "AppendEntriesReq",
                                from |-> n, to |-> m,
                                term |-> CurrentTerm[n],
                                prevLogIndex |-> NextIndex[n][m] - 1,
                                prevLogTerm |-> TermAt(n, NextIndex[n][m] - 1),
                                entries |-> ents,
                                leaderCommit |-> CommitIndex[n],
                                msgId |-> MsgId[n] + 1] }
               /\ MsgId' = [MsgId EXCEPT ![n] = MsgId[n] + 1]
               /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Members, Voting, VotesGranted, PreVotesGranted >>

RecvAppendEntries ==
    \E m \in Net:
      /\ IsAEReq(m)
      /\ LET r == m.to IN
         LET s == m.from IN
         LET termLT == m.term < CurrentTerm[r] IN
         IF termLT THEN
           /\ Net' = (Net \ {m}) \cup { [type |-> "AppendEntriesResp",
                                         from |-> r, to |-> s,
                                         term |-> CurrentTerm[r],
                                         success |-> FALSE,
                                         matchIndex |-> LastIndex(r),
                                         msgId |-> m.msgId] }
           /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, TimeoutElapsed, ETimeoutRand, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Members, Voting, VotesGranted, PreVotesGranted >>
         ELSE
           LET CurrentTerm1 == IF m.term > CurrentTerm[r] THEN [CurrentTerm EXCEPT ![r] = m.term] ELSE CurrentTerm IN
           LET State1 == IF m.term > CurrentTerm[r] THEN [State EXCEPT ![r] = "FOLLOWER"] ELSE State IN
           LET VotedFor1 == IF m.term > CurrentTerm[r] THEN [VotedFor EXCEPT ![r] = None] ELSE VotedFor IN
           LET LeaderId1 == [LeaderId EXCEPT ![r] = s] IN
           LET TimeoutElapsed1 == [TimeoutElapsed EXCEPT ![r] = 0] IN
           LET BaseOk == (m.prevLogIndex = Base(r) /\ m.prevLogTerm = BaseTerm(r)) IN
           LET PrevOk == BaseOk \/ (HasEntryAt(r, m.prevLogIndex) /\ TermAt(r, m.prevLogIndex) = m.prevLogTerm) IN
           IF ~PrevOk THEN
             /\ LET matchIdxR == Min(LastIndex(r), m.prevLogIndex) IN
                /\ Net' = (Net \ {m}) \cup { [type |-> "AppendEntriesResp",
                                              from |-> r, to |-> s,
                                              term |-> CurrentTerm1[r],
                                              success |-> FALSE,
                                              matchIndex |-> matchIdxR,
                                              msgId |-> m.msgId] }
                /\ CurrentTerm' = CurrentTerm1
                /\ State' = State1
                /\ VotedFor' = VotedFor1
                /\ LeaderId' = LeaderId1
                /\ TimeoutElapsed' = TimeoutElapsed1
                /\ HBElapsed' = HBElapsed
                /\ MsgId' = MsgId
                /\ Log' = Log
                /\ CommitIndex' = CommitIndex
                /\ LastApplied' = LastApplied
                /\ SnapshotLastIndex' = SnapshotLastIndex
                /\ SnapshotLastTerm' = SnapshotLastTerm
                /\ SnapshotInProgress' = SnapshotInProgress
                /\ NextSnapIndex' = NextSnapIndex
                /\ NextSnapTerm' = NextSnapTerm
                /\ NextIndex' = NextIndex
                /\ MatchIndex' = MatchIndex
                /\ Members' = Members
                /\ Voting' = Voting
                /\ VotesGranted' = VotesGranted
                /\ PreVotesGranted' = PreVotesGranted
           ELSE
             LET eSeq == m.entries IN
             LET first == m.prevLogIndex + 1 IN
             LET nEnt == Len(eSeq) IN
             LET J == { j \in 1..nEnt :
                         HasEntryAt(r, first + j - 1)
                         /\ EntryAt(r, first + j - 1).term # eSeq[j].term } IN
             LET l == IF J = {} THEN nEnt + 1 ELSE Min(J) IN
             LET LogPre ==
                 IF l = nEnt + 1 THEN
                   Log[r]
                 ELSE
                   SubSeq(Log[r], 1, Max(0, Pos(r, first + l - 2))) IN
             LET AppSeq ==
                 IF l = nEnt + 1 THEN
                   IF first + nEnt - 1 <= LastIndex(r)
                   THEN <<>>
                   ELSE SubSeq(eSeq, (LastIndex(r) - m.prevLogIndex) + 1, nEnt)
                 ELSE
                   SubSeq(eSeq, l, nEnt) IN
             LET Log1 == AppendSeq(LogPre, AppSeq) IN
             LET matchIdxR == Base(r) + Len(Log1) IN
             LET CommitIndex1 == [CommitIndex EXCEPT ![r] = Min(m.leaderCommit, Base(r) + Len(Log1))] IN
             /\ Net' = (Net \ {m}) \cup { [type |-> "AppendEntriesResp",
                                           from |-> r, to |-> s,
                                           term |-> CurrentTerm1[r],
                                           success |-> TRUE,
                                           matchIndex |-> matchIdxR,
                                           msgId |-> m.msgId] }
             /\ CurrentTerm' = CurrentTerm1
             /\ State' = State1
             /\ VotedFor' = VotedFor1
             /\ LeaderId' = LeaderId1
             /\ TimeoutElapsed' = TimeoutElapsed1
             /\ HBElapsed' = HBElapsed
             /\ MsgId' = MsgId
             /\ Log' = [Log EXCEPT ![r] = Log1]
             /\ CommitIndex' = CommitIndex1
             /\ LastApplied' = LastApplied
             /\ SnapshotLastIndex' = SnapshotLastIndex
             /\ SnapshotLastTerm' = SnapshotLastTerm
             /\ SnapshotInProgress' = SnapshotInProgress
             /\ NextSnapIndex' = NextSnapIndex
             /\ NextSnapTerm' = NextSnapTerm
             /\ NextIndex' = NextIndex
             /\ MatchIndex' = MatchIndex
             /\ Members' = Members
             /\ Voting' = Voting
             /\ VotesGranted' = VotesGranted
             /\ PreVotesGranted' = PreVotesGranted

RecvAppendEntriesResponse ==
    \E m \in Net:
      /\ IsAEResp(m)
      /\ LET l == m.to IN
         LET f == m.from IN
         IF State[l] # "LEADER" THEN
           /\ Net' = Net \ {m}
           /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Members, Voting, VotesGranted, PreVotesGranted >>
         ELSE
           IF m.term > CurrentTerm[l] THEN
             /\ Net' = Net \ {m}
             /\ CurrentTerm' = [CurrentTerm EXCEPT ![l] = m.term]
             /\ State' = [State EXCEPT ![l] = "FOLLOWER"]
             /\ VotedFor' = [VotedFor EXCEPT ![l] = None]
             /\ LeaderId' = [LeaderId EXCEPT ![l] = None]
             /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![l] = 0]
             /\ HBElapsed' = HBElapsed
             /\ MsgId' = MsgId
             /\ Log' = Log
             /\ CommitIndex' = CommitIndex
             /\ LastApplied' = LastApplied
             /\ SnapshotLastIndex' = SnapshotLastIndex
             /\ SnapshotLastTerm' = SnapshotLastTerm
             /\ SnapshotInProgress' = SnapshotInProgress
             /\ NextSnapIndex' = NextSnapIndex
             /\ NextSnapTerm' = NextSnapTerm
             /\ NextIndex' = NextIndex
             /\ MatchIndex' = MatchIndex
             /\ Members' = Members
             /\ Voting' = Voting
             /\ VotesGranted' = VotesGranted
             /\ PreVotesGranted' = PreVotesGranted
           ELSE
             /\ Net' = Net \ {m}
             /\ IF m.success THEN
                   /\ MatchIndex' = [MatchIndex EXCEPT ![l][f] = m.matchIndex]
                   /\ NextIndex' = [NextIndex EXCEPT ![l][f] = m.matchIndex + 1]
                ELSE
                   /\ MatchIndex' = MatchIndex
                   /\ NextIndex' = [NextIndex EXCEPT ![l][f] = Max(Base(l) + 1, NextIndex[l][f] - 1)]
             /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, Members, Voting, VotesGranted, PreVotesGranted >>

LogCommit(l) ==
    /\ State[l] = "LEADER"
    /\ \E j \in Nat:
        /\ j > CommitIndex[l]
        /\ j <= LastIndex(l)
        /\ Log[l][Pos(l, j)].term = CurrentTerm[l]
        /\ Cardinality({ v \in Voting : IF v = l THEN LastIndex(l) >= j ELSE MatchIndex[l][v] >= j }) >= MajoritySize(Voting)
        /\ CommitIndex' = [CommitIndex EXCEPT ![l] = j]
        /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, Log, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

LogAppend(n) ==
    /\ State[n] = "LEADER"
    /\ \E e \in [term: {CurrentTerm[n]}, etype: {"data"}, node: {None}]:
        /\ Entry(e)
        /\ Log' = [Log EXCEPT ![n] = Log[n] \o << e >>]
        /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

LogDelete(n, idx) ==
    /\ idx > CommitIndex[n]
    /\ idx >= Base(n) + 1
    /\ idx <= LastIndex(n)
    /\ Log' = [Log EXCEPT ![n] = SubSeq(Log[n], 1, Pos(n, idx - 1))]
    /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

RecvRequestVote ==
    \E m \in Net:
      /\ IsRVReq(m)
      /\ LET r == m.to IN
         LET upTo == UpToDate(m.lastLogIndex, m.lastLogTerm, LastIndex(r), TermAt(r, LastIndex(r))) IN
         LET CurrentTerm1 == IF ~m.prevote /\ m.term > CurrentTerm[r] THEN [CurrentTerm EXCEPT ![r] = m.term] ELSE CurrentTerm IN
         LET State1 == IF ~m.prevote /\ m.term > CurrentTerm[r] THEN [State EXCEPT ![r] = "FOLLOWER"] ELSE State IN
         LET VotedFor1 == IF ~m.prevote /\ m.term > CurrentTerm[r] THEN [VotedFor EXCEPT ![r] = None] ELSE VotedFor IN
         LET CanGrant ==
             IF m.prevote THEN
               /\ (LeaderId[r] = None \/ TimeoutElapsed[r] >= ETimeoutRand[r])
               /\ upTo
             ELSE
               /\ (VotedFor1[r] = None \/ VotedFor1[r] = m.from)
               /\ upTo IN
         LET voteR == CanGrant IN
         LET VotedFor2 == IF m.prevote THEN VotedFor1 ELSE [VotedFor1 EXCEPT ![r] = IF CanGrant THEN m.from ELSE VotedFor1[r]] IN
         LET LeaderId2 == IF m.prevote THEN LeaderId ELSE [LeaderId EXCEPT ![r] = None] IN
         LET TimeoutElapsed2 == IF m.prevote THEN TimeoutElapsed ELSE [TimeoutElapsed EXCEPT ![r] = 0] IN
         /\ Net' = (Net \ {m}) \cup { [type |-> "RequestVoteResp",
                                       from |-> r, to |-> m.from,
                                       prevote |-> m.prevote,
                                       requestTerm |-> m.term,
                                       term |-> CurrentTerm1[r],
                                       voteGranted |-> voteR] }
         /\ CurrentTerm' = CurrentTerm1
         /\ State' = State1
         /\ VotedFor' = VotedFor2
         /\ LeaderId' = LeaderId2
         /\ TimeoutElapsed' = TimeoutElapsed2
         /\ UNCHANGED << ETimeoutRand, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Members, Voting, VotesGranted, PreVotesGranted >>

RecvRequestVoteResponse ==
    \E m \in Net:
      /\ IsRVResp(m)
      /\ LET c == m.to IN
         /\ Net' = Net \ {m}
         /\ IF m.term > CurrentTerm[c] THEN
               /\ CurrentTerm' = [CurrentTerm EXCEPT ![c] = m.term]
               /\ State' = [State EXCEPT ![c] = "FOLLOWER"]
               /\ VotedFor' = [VotedFor EXCEPT ![c] = None]
               /\ LeaderId' = [LeaderId EXCEPT ![c] = None]
               /\ TimeoutElapsed' = [TimeoutElapsed EXCEPT ![c] = 0]
               /\ UNCHANGED << ETimeoutRand, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Members, Voting, VotesGranted, PreVotesGranted >>
            ELSE
               /\ IF m.prevote THEN
                     /\ State[c] = "PRECANDIDATE"
                     /\ m.requestTerm = CurrentTerm[c] + 1
                     /\ PreVotesGranted' = [PreVotesGranted EXCEPT ![c] = IF m.voteGranted THEN PreVotesGranted[c] \cup {m.from} ELSE PreVotesGranted[c]]
                     /\ VotesGranted' = VotesGranted
                     /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Members, Voting >>
                  ELSE
                     /\ State[c] = "CANDIDATE"
                     /\ m.requestTerm = CurrentTerm[c]
                     /\ VotesGranted' = [VotesGranted EXCEPT ![c] = IF m.voteGranted THEN VotesGranted[c] \cup {m.from} ELSE VotesGranted[c]]
                     /\ PreVotesGranted' = PreVotesGranted
                     /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Members, Voting >>

AddNode(n, x) ==
    /\ State[n] = "LEADER"
    /\ x \in Nodes \ Members
    /\ Log' = [Log EXCEPT ![n] = Log[n] \o << [term |-> CurrentTerm[n], etype |-> "add_node", node |-> x] >>]
    /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

RemoveNode(n, x) ==
    /\ State[n] = "LEADER"
    /\ x \in Members
    /\ Log' = [Log EXCEPT ![n] = Log[n] \o << [term |-> CurrentTerm[n], etype |-> "remove_node", node |-> x] >>]
    /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

AddNonVotingNode(n, x) ==
    /\ State[n] = "LEADER"
    /\ x \in Nodes \ Members
    /\ Log' = [Log EXCEPT ![n] = Log[n] \o << [term |-> CurrentTerm[n], etype |-> "add_nonvoting_node", node |-> x] >>]
    /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

ApplyConfigChange(n) ==
    /\ LastApplied[n] < CommitIndex[n]
    /\ HasEntryAt(n, LastApplied[n] + 1)
    /\ LET i == LastApplied[n] + 1 IN
       LET e == EntryAt(n, i) IN
       /\ e.etype \in {"add_node", "add_nonvoting_node", "remove_node"}
       /\ LastApplied' = [LastApplied EXCEPT ![n] = i]
       /\ Members' =
           IF e.etype = "add_node" THEN Members \cup {e.node}
           ELSE IF e.etype = "add_nonvoting_node" THEN Members \cup {e.node}
           ELSE Members \ {e.node}
       /\ Voting' =
           IF e.etype = "add_node" THEN Voting \cup {e.node}
           ELSE IF e.etype = "add_nonvoting_node" THEN Voting
           ELSE Voting \ {e.node}
       /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, Log, CommitIndex, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, VotesGranted, PreVotesGranted >>

ApplyEntry(n) ==
    /\ LastApplied[n] < CommitIndex[n]
    /\ HasEntryAt(n, LastApplied[n] + 1)
    /\ LET i == LastApplied[n] + 1 IN
       LET e == EntryAt(n, i) IN
       /\ e.etype \notin {"add_node","add_nonvoting_node","remove_node"}
       /\ LastApplied' = [LastApplied EXCEPT ![n] = i]
       /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, Log, CommitIndex, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

SnapshotBegin(n) ==
    /\ ~SnapshotInProgress[n]
    /\ LastApplied[n] > SnapshotLastIndex[n]
    /\ LastApplied[n] - SnapshotLastIndex[n] >= SNAPSHOT_THRESHOLD
    /\ SnapshotInProgress' = [SnapshotInProgress EXCEPT ![n] = TRUE]
    /\ NextSnapIndex' = [NextSnapIndex EXCEPT ![n] = LastApplied[n]]
    /\ NextSnapTerm' = [NextSnapTerm EXCEPT ![n] = TermAt(n, LastApplied[n])]
    /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

SnapshotEnd(n) ==
    /\ SnapshotInProgress[n]
    /\ SnapshotLastIndex' = [SnapshotLastIndex EXCEPT ![n] = NextSnapIndex[n]]
    /\ SnapshotLastTerm' = [SnapshotLastTerm EXCEPT ![n] = NextSnapTerm[n]]
    /\ LET oldBase == Base(n) IN
       LET newBase == NextSnapIndex[n] IN
       LET cutPos == Max(0, newBase - oldBase) IN
       /\ Log' = [Log EXCEPT ![n] = SubSeq(Log[n], cutPos + 1, LenLog(n))]
    /\ SnapshotInProgress' = [SnapshotInProgress EXCEPT ![n] = FALSE]
    /\ UNCHANGED << State, CurrentTerm, VotedFor, LeaderId, ETimeoutRand, TimeoutElapsed, HBElapsed, MsgId, CommitIndex, LastApplied, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

Next ==
    \/ \E n \in Nodes: PeriodicElectionTimeout(n)
    \/ \E n \in Nodes: PeriodicHeartbeat(n)
    \/ \E n \in Nodes: ElectionTimeout(n)
    \/ \E n \in Nodes: ElectionStart(n)
    \/ \E n \in Nodes: SendHeartbeat(n)
    \/ \E n \in Nodes: \E m \in Members \ {n}: SendAppendEntries(n, m)
    \/ RecvAppendEntries
    \/ RecvAppendEntriesResponse
    \/ RecvRequestVote
    \/ RecvRequestVoteResponse
    \/ \E n \in Nodes: LogAppend(n)
    \/ \E l \in Nodes: LogCommit(l)
    \/ \E n \in Nodes: \E idx \in Nat: LogDelete(n, idx)
    \/ \E n \in Nodes: \E x \in Nodes: AddNode(n, x)
    \/ \E n \in Nodes: \E x \in Nodes: AddNonVotingNode(n, x)
    \/ \E n \in Nodes: \E x \in Nodes: RemoveNode(n, x)
    \/ \E n \in Nodes: ApplyConfigChange(n)
    \/ \E n \in Nodes: ApplyEntry(n)
    \/ \E n \in Nodes: SnapshotBegin(n)
    \/ \E n \in Nodes: SnapshotEnd(n)

Spec ==
    Init /\ [][Next]_<< State, CurrentTerm, VotedFor, LeaderId, TimeoutElapsed, ETimeoutRand, HBElapsed, MsgId, Log, CommitIndex, LastApplied, SnapshotLastIndex, SnapshotLastTerm, SnapshotInProgress, NextSnapIndex, NextSnapTerm, NextIndex, MatchIndex, Net, Members, Voting, VotesGranted, PreVotesGranted >>

====