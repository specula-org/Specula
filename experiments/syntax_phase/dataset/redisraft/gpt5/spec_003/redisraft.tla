---- MODULE redisraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets

CONSTANTS
    NODE_IDS,
    InitNodeSet,
    InitVoting,
    ELECTION_TIMEOUT,
    HEARTBEAT_TIMEOUT,
    None

ASSUME None \notin NODE_IDS

RoleSet == {"FOLLOWER","PRECANDIDATE","CANDIDATE","LEADER"}

EntryType == {"NoOp","Data","AddNode","AddNonVoting","RemoveNode"}

Entry == [term: Nat, etype: EntryType, node: NODE_IDS \cup {None}]

MsgType == {"RequestVote","RequestVoteResp","AppendEntries","AppendEntriesResp"}

Msg ==
    { [mtype |-> "RequestVote",
       prevote |-> b,
       term |-> t,
       src |-> i,
       dst |-> j,
       candidate |-> i,
       lastLogIndex |-> lli,
       lastLogTerm |-> llt] :
         b \in BOOLEAN /\ t \in Nat /\ i \in NODE_IDS /\ j \in NODE_IDS /\
         lli \in Nat /\ llt \in Nat } \cup
    { [mtype |-> "RequestVoteResp",
       prevote |-> b,
       requestTerm |-> rterm,
       term |-> t,
       src |-> i,
       dst |-> j,
       voteGranted |-> vg] :
         b \in BOOLEAN /\ rterm \in Nat /\ t \in Nat /\ i \in NODE_IDS /\ j \in NODE_IDS /\ vg \in BOOLEAN } \cup
    { [mtype |-> "AppendEntries",
       term |-> t,
       leaderId |-> i,
       src |-> i,
       dst |-> j,
       prevLogIndex |-> pli,
       prevLogTerm |-> plt,
       leaderCommit |-> lc,
       entries |-> es] :
         t \in Nat /\ i \in NODE_IDS /\ j \in NODE_IDS /\ pli \in Nat /\ plt \in Nat /\ lc \in Nat /\ es \in Seq(Entry) } \cup
    { [mtype |-> "AppendEntriesResp",
       term |-> t,
       src |-> i,
       dst |-> j,
       success |-> s,
       currentIndex |-> ci] :
         t \in Nat /\ i \in NODE_IDS /\ j \in NODE_IDS /\ s \in BOOLEAN /\ ci \in Nat }

VARIABLES
    NodeSet,
    Voting,
    Active,
    Role,
    CurrentTerm,
    VotedFor,
    LeaderId,
    Log,
    CommitIndex,
    LastApplied,
    NextIndex,
    MatchIndex,
    ElectionElapsed,
    ElectionDeadline,
    HBElapsed,
    Messages,
    SnapLastIndex,
    SnapLastTerm,
    SnapshotInProgress,
    NextSnapshotIndex,
    PreVotesReceived,
    VotesReceived,
    PendingDelete

vars == << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

Voters == { n \in NodeSet : Voting[n] }

Majority(k) == k >= (Cardinality(Voters) \div 2) + 1

LastLogIndex(n) == SnapLastIndex[n] + Len(Log[n])

LastLogTerm(n) == IF Len(Log[n]) = 0 THEN SnapLastTerm[n] ELSE Log[n][Len(Log[n])].term

IndexToPos(n, idx) == idx - SnapLastIndex[n]

GetTermAt(n, idx) ==
    IF idx = SnapLastIndex[n] THEN SnapLastTerm[n]
    ELSE IF idx > SnapLastIndex[n] /\ idx <= LastLogIndex(n)
         THEN Log[n][IndexToPos(n, idx)].term
         ELSE 0

DropFrom(n, idx) ==
    IF idx <= SnapLastIndex[n] THEN Log[n]
    ELSE IF idx > LastLogIndex(n) THEN Log[n]
    ELSE SubSeq(Log[n], 1, IndexToPos(n, idx) - 1)

MaxNat(x,y) == IF x >= y THEN x ELSE y
MinNat(x,y) == IF x <= y THEN x ELSE y

Init ==
    NodeSet \in SUBSET NODE_IDS /\
    NodeSet = InitNodeSet /\
    Voting \in [NODE_IDS -> BOOLEAN] /\
    \A n \in NODE_IDS : Voting[n] = (n \in InitVoting) /\
    Active \in [NODE_IDS -> BOOLEAN] /\
    \A n \in NODE_IDS : Active[n] = (n \in InitNodeSet) /\
    Role \in [NODE_IDS -> RoleSet] /\
    \A n \in NODE_IDS : Role[n] = "FOLLOWER" /\
    CurrentTerm \in [NODE_IDS -> Nat] /\
    \A n \in NODE_IDS : CurrentTerm[n] = 0 /\
    VotedFor \in [NODE_IDS -> (NODE_IDS \cup {None})] /\
    \A n \in NODE_IDS : VotedFor[n] = None /\
    LeaderId \in [NODE_IDS -> (NODE_IDS \cup {None})] /\
    \A n \in NODE_IDS : LeaderId[n] = None /\
    Log \in [NODE_IDS -> Seq(Entry)] /\
    \A n \in NODE_IDS : Log[n] = << >> /\
    CommitIndex \in [NODE_IDS -> Nat] /\ \A n \in NODE_IDS : CommitIndex[n] = 0 /\
    LastApplied \in [NODE_IDS -> Nat] /\ \A n \in NODE_IDS : LastApplied[n] = 0 /\
    NextIndex \in [NODE_IDS -> [NODE_IDS -> Nat]] /\ NextIndex = [i \in NODE_IDS |-> [j \in NODE_IDS |-> 1]] /\
    MatchIndex \in [NODE_IDS -> [NODE_IDS -> Nat]] /\ MatchIndex = [i \in NODE_IDS |-> [j \in NODE_IDS |-> 0]] /\
    ElectionElapsed \in [NODE_IDS -> Nat] /\ \A n \in NODE_IDS : ElectionElapsed[n] = 0 /\
    ElectionDeadline \in [NODE_IDS -> (ELECTION_TIMEOUT..(2*ELECTION_TIMEOUT))] /\
    HBElapsed \in [NODE_IDS -> Nat] /\ \A n \in NODE_IDS : HBElapsed[n] = 0 /\
    Messages \in SUBSET Msg /\ Messages = {} /\
    SnapLastIndex \in [NODE_IDS -> Nat] /\ \A n \in NODE_IDS : SnapLastIndex[n] = 0 /\
    SnapLastTerm \in [NODE_IDS -> Nat] /\ \A n \in NODE_IDS : SnapLastTerm[n] = 0 /\
    SnapshotInProgress \in [NODE_IDS -> BOOLEAN] /\ \A n \in NODE_IDS : SnapshotInProgress[n] = FALSE /\
    NextSnapshotIndex \in [NODE_IDS -> Nat] /\ \A n \in NODE_IDS : NextSnapshotIndex[n] = 0 /\
    PreVotesReceived \in [NODE_IDS -> SUBSET NODE_IDS] /\ \A n \in NODE_IDS : PreVotesReceived[n] = {} /\
    VotesReceived \in [NODE_IDS -> SUBSET NODE_IDS] /\ \A n \in NODE_IDS : VotesReceived[n] = {} /\
    PendingDelete \in [NODE_IDS -> Nat] /\ \A n \in NODE_IDS : PendingDelete[n] = 0

BecomeFollower(n) ==
    n \in NodeSet /\ Role[n] # "FOLLOWER" /\
    \E d \in ELECTION_TIMEOUT..(2*ELECTION_TIMEOUT) :
      Role' = [Role EXCEPT ![n] = "FOLLOWER"] /\
      LeaderId' = [LeaderId EXCEPT ![n] = None] /\
      ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0] /\
      ElectionDeadline' = [ElectionDeadline EXCEPT ![n] = d] /\
      UNCHANGED << NodeSet, Voting, Active, CurrentTerm, VotedFor, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

BecomePreCandidate(n) ==
    n \in NodeSet /\ Role[n] = "FOLLOWER" /\
    \E d \in ELECTION_TIMEOUT..(2*ELECTION_TIMEOUT) :
      Role' = [Role EXCEPT ![n] = "PRECANDIDATE"] /\
      PreVotesReceived' = [PreVotesReceived EXCEPT ![n] = (IF Voting[n] THEN {n} ELSE {})] /\
      ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0] /\
      ElectionDeadline' = [ElectionDeadline EXCEPT ![n] = d] /\
      UNCHANGED << NodeSet, Voting, Active, CurrentTerm, VotedFor, LeaderId, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, VotesReceived, PendingDelete >>

BecomeCandidate(n) ==
    n \in NodeSet /\ Role[n] \in {"FOLLOWER","PRECANDIDATE"} /\
    \E d \in ELECTION_TIMEOUT..(2*ELECTION_TIMEOUT) :
      CurrentTerm' = [CurrentTerm EXCEPT ![n] = @ + 1] /\
      Role' = [Role EXCEPT ![n] = "CANDIDATE"] /\
      VotedFor' = [VotedFor EXCEPT ![n] = n] /\
      VotesReceived' = [VotesReceived EXCEPT ![n] = (IF Voting[n] THEN {n} ELSE {})] /\
      LeaderId' = [LeaderId EXCEPT ![n] = None] /\
      ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0] /\
      ElectionDeadline' = [ElectionDeadline EXCEPT ![n] = d] /\
      UNCHANGED << NodeSet, Voting, Active, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, PendingDelete >>

BecomeLeader(n) ==
    n \in NodeSet /\ Role[n] = "CANDIDATE" /\
    Role' = [Role EXCEPT ![n] = "LEADER"] /\
    LeaderId' = [LeaderId EXCEPT ![n] = n] /\
    Log' = [Log EXCEPT ![n] = @ \o << [term |-> CurrentTerm[n], etype |-> "NoOp", node |-> None] >>] /\
    NextIndex' = [NextIndex EXCEPT ![n] = [p \in NODE_IDS |-> LastLogIndex(n) + 1]] /\
    MatchIndex' = [MatchIndex EXCEPT ![n] = [p \in NODE_IDS |-> 0]] /\
    HBElapsed' = [HBElapsed EXCEPT ![n] = 0] /\
    UNCHANGED << NodeSet, Voting, Active, CurrentTerm, VotedFor, CommitIndex, LastApplied, ElectionElapsed, ElectionDeadline, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

ElectionTimeout(n) ==
    n \in NodeSet /\ Role[n] # "LEADER" /\ ElectionElapsed[n] >= ElectionDeadline[n] /\
    \E d \in ELECTION_TIMEOUT..(2*ELECTION_TIMEOUT) :
      Role' = [Role EXCEPT ![n] = "PRECANDIDATE"] /\
      PreVotesReceived' = [PreVotesReceived EXCEPT ![n] = (IF Voting[n] THEN {n} ELSE {})] /\
      ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = 0] /\
      ElectionDeadline' = [ElectionDeadline EXCEPT ![n] = d] /\
      LeaderId' = [LeaderId EXCEPT ![n] = None] /\
      UNCHANGED << NodeSet, Voting, Active, CurrentTerm, VotedFor, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, VotesReceived, PendingDelete >>

ElectionStart(n) ==
    n \in NodeSet /\ (Role[n] = "PRECANDIDATE" \/ Role[n] = "CANDIDATE") /\
    \E p \in NodeSet :
      p # n /\ Active[p] /\ Voting[p] /\
      Messages' = Messages \cup
        (IF Role[n] = "PRECANDIDATE"
         THEN { [mtype |-> "RequestVote", prevote |-> TRUE, term |-> CurrentTerm[n] + 1, src |-> n, dst |-> p, candidate |-> n, lastLogIndex |-> LastLogIndex(n), lastLogTerm |-> LastLogTerm(n) ] }
         ELSE { [mtype |-> "RequestVote", prevote |-> FALSE, term |-> CurrentTerm[n], src |-> n, dst |-> p, candidate |-> n, lastLogIndex |-> LastLogIndex(n), lastLogTerm |-> LastLogTerm(n) ] }) /\
    UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

RecvRequestVote ==
    \E m \in Messages :
      m.mtype = "RequestVote" /\
      LET j == m.dst IN
      j \in NodeSet /\ Active[j] /\
      LET logUp == (m.lastLogTerm > LastLogTerm(j)) \/ (m.lastLogTerm = LastLogTerm(j) /\ m.lastLogIndex >= LastLogIndex(j)) IN
      LET needStepDown == (~m.prevote /\ m.term > CurrentTerm[j]) IN
      LET newTermJ == IF needStepDown THEN m.term ELSE CurrentTerm[j] IN
      LET newRoleJ == IF needStepDown THEN "FOLLOWER" ELSE Role[j] IN
      LET newLeaderJ == IF needStepDown THEN None ELSE LeaderId[j] IN
      LET votedForBase == IF needStepDown THEN None ELSE VotedFor[j] IN
      LET grantPrevote == (m.prevote /\ m.term >= CurrentTerm[j] /\ logUp) IN
      LET grantVote == (~m.prevote /\ m.term = newTermJ /\ (votedForBase = None \/ votedForBase = m.candidate) /\ logUp) IN
      LET voteGranted == grantPrevote \/ grantVote IN
      LET vfNew == IF grantVote THEN m.candidate ELSE votedForBase IN
      \E d \in ELECTION_TIMEOUT..(2*ELECTION_TIMEOUT) :
        Messages' = (Messages \ {m}) \cup
          { [mtype |-> "RequestVoteResp",
             prevote |-> m.prevote,
             requestTerm |-> m.term,
             term |-> (IF m.prevote THEN CurrentTerm[j] ELSE newTermJ),
             src |-> j,
             dst |-> m.src,
             voteGranted |-> voteGranted] } /\
        CurrentTerm' = [CurrentTerm EXCEPT ![j] = newTermJ] /\
        Role' = [Role EXCEPT ![j] = newRoleJ] /\
        VotedFor' = [VotedFor EXCEPT ![j] = vfNew] /\
        LeaderId' = [LeaderId EXCEPT ![j] = newLeaderJ] /\
        ElectionElapsed' = IF needStepDown THEN [ElectionElapsed EXCEPT ![j] = 0] ELSE ElectionElapsed /\
        ElectionDeadline' = IF needStepDown THEN [ElectionDeadline EXCEPT ![j] = d] ELSE ElectionDeadline /\
        UNCHANGED << NodeSet, Voting, Active, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, HBElapsed, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

RecvRequestVoteResponse ==
    \E m \in Messages :
      m.mtype = "RequestVoteResp" /\
      LET n == m.dst IN
      n \in NodeSet /\ Active[n] /\
      LET stepDown == m.term > CurrentTerm[n] IN
      LET condPrev == (m.prevote /\ Role[n] = "PRECANDIDATE" /\ m.requestTerm = CurrentTerm[n] + 1 /\ m.voteGranted /\ ~stepDown) IN
      LET condVote == (~m.prevote /\ Role[n] = "CANDIDATE" /\ m.requestTerm = CurrentTerm[n] /\ m.voteGranted /\ ~stepDown) IN
      LET preSet == PreVotesReceived[n] \cup {m.src} IN
      LET voteSet == VotesReceived[n] \cup {m.src} IN
      LET preMaj == Majority(Cardinality(preSet)) IN
      LET voteMaj == Majority(Cardinality(voteSet)) IN
      Messages' = Messages \ {m} /\
      CurrentTerm' =
        IF stepDown THEN [CurrentTerm EXCEPT ![n] = m.term]
        ELSE IF condPrev /\ preMaj THEN [CurrentTerm EXCEPT ![n] = @ + 1]
        ELSE CurrentTerm /\
      Role' =
        IF stepDown THEN [Role EXCEPT ![n] = "FOLLOWER"]
        ELSE IF condPrev /\ preMaj THEN [Role EXCEPT ![n] = "CANDIDATE"]
        ELSE IF condVote /\ voteMaj THEN [Role EXCEPT ![n] = "LEADER"]
        ELSE Role /\
      VotedFor' =
        IF stepDown THEN [VotedFor EXCEPT ![n] = None]
        ELSE IF condPrev /\ preMaj THEN [VotedFor EXCEPT ![n] = n]
        ELSE VotedFor /\
      LeaderId' =
        IF stepDown THEN [LeaderId EXCEPT ![n] = None]
        ELSE IF condVote /\ voteMaj THEN [LeaderId EXCEPT ![n] = n]
        ELSE LeaderId /\
      PreVotesReceived' =
        IF condPrev THEN [PreVotesReceived EXCEPT ![n] = preSet] ELSE PreVotesReceived /\
      VotesReceived' =
        IF condVote THEN [VotesReceived EXCEPT ![n] = voteSet] ELSE VotesReceived /\
      Log' =
        IF condVote /\ voteMaj
        THEN [Log EXCEPT ![n] = @ \o << [term |-> CurrentTerm[n], etype |-> "NoOp", node |-> None] >>]
        ELSE Log /\
      NextIndex' =
        IF condVote /\ voteMaj
        THEN [NextIndex EXCEPT ![n] = [p \in NODE_IDS |-> LastLogIndex(n) + 1]]
        ELSE NextIndex /\
      MatchIndex' =
        IF condVote /\ voteMaj
        THEN [MatchIndex EXCEPT ![n] = [p \in NODE_IDS |-> 0]]
        ELSE MatchIndex /\
      UNCHANGED << NodeSet, Voting, Active, CommitIndex, LastApplied, ElectionElapsed, ElectionDeadline, HBElapsed, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PendingDelete >>

SendAppendEntries ==
    \E l \in NodeSet, f \in NodeSet :
      Role[l] = "LEADER" /\ l # f /\ Active[f] /\
      LET next == NextIndex[l][f] IN
      SnapLastIndex[l] < next /\
      Messages' = Messages \cup
         { [mtype |-> "AppendEntries",
            term |-> CurrentTerm[l],
            leaderId |-> l,
            src |-> l,
            dst |-> f,
            prevLogIndex |-> next - 1,
            prevLogTerm |-> GetTermAt(l, next - 1),
            leaderCommit |-> CommitIndex[l],
            entries |-> IF next <= LastLogIndex(l) THEN SubSeq(Log[l], IndexToPos(l, next), Len(Log[l])) ELSE << >> ] } /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

SendHeartbeat ==
    \E l \in NodeSet, f \in NodeSet :
      Role[l] = "LEADER" /\ l # f /\ Active[f] /\
      Messages' = Messages \cup
        { [mtype |-> "AppendEntries",
           term |-> CurrentTerm[l],
           leaderId |-> l,
           src |-> l,
           dst |-> f,
           prevLogIndex |-> LastLogIndex(l),
           prevLogTerm |-> LastLogTerm(l),
           leaderCommit |-> CommitIndex[l],
           entries |-> << >> ] } /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

RecvAppendEntries ==
    \E m \in Messages :
      m.mtype = "AppendEntries" /\
      LET j == m.dst IN
      j \in NodeSet /\ Active[j] /\
      LET matchPrev ==
         (m.prevLogIndex = SnapLastIndex[j] /\ m.prevLogTerm = SnapLastTerm[j]) \/
         (m.prevLogIndex > SnapLastIndex[j] /\ m.prevLogIndex <= LastLogIndex(j) /\ GetTermAt(j, m.prevLogIndex) = m.prevLogTerm) IN
      LET success == (m.term >= CurrentTerm[j]) /\ matchPrev IN
      LET newIndex == IF m.entries = << >> THEN (IF m.prevLogIndex <= LastLogIndex(j) THEN m.prevLogIndex ELSE LastLogIndex(j)) ELSE m.prevLogIndex + Len(m.entries) IN
      LET needStepDown == m.term > CurrentTerm[j] IN
      \E d \in ELECTION_TIMEOUT..(2*ELECTION_TIMEOUT) :
        Messages' = (Messages \ {m}) \cup
          { [mtype |-> "AppendEntriesResp",
             term |-> IF m.term >= CurrentTerm[j] THEN m.term ELSE CurrentTerm[j],
             src |-> j,
             dst |-> m.src,
             success |-> success,
             currentIndex |-> newIndex ] } /\
        CurrentTerm' = IF needStepDown THEN [CurrentTerm EXCEPT ![j] = m.term] ELSE CurrentTerm /\
        Role' = IF needStepDown THEN [Role EXCEPT ![j] = "FOLLOWER"] ELSE Role /\
        VotedFor' = IF needStepDown THEN [VotedFor EXCEPT ![j] = None] ELSE VotedFor /\
        LeaderId' = [LeaderId EXCEPT ![j] = m.leaderId] /\
        ElectionElapsed' = IF needStepDown THEN [ElectionElapsed EXCEPT ![j] = 0] ELSE ElectionElapsed /\
        ElectionDeadline' = IF needStepDown THEN [ElectionDeadline EXCEPT ![j] = d] ELSE ElectionDeadline /\
        Log' =
          IF success
          THEN [Log EXCEPT ![j] =
                IF Len(m.entries) = 0
                THEN @
                ELSE LET pos == IndexToPos(j, m.prevLogIndex) IN
                     (IF pos = 0 THEN << >> ELSE SubSeq(@, 1, pos)) \o m.entries ]
          ELSE Log /\
        CommitIndex' =
          IF success /\ m.leaderCommit > CommitIndex[j]
          THEN [CommitIndex EXCEPT ![j] = MinNat(m.leaderCommit, newIndex)]
          ELSE CommitIndex /\
        PendingDelete' =
          IF success
          THEN PendingDelete
          ELSE [PendingDelete EXCEPT ![j] = m.prevLogIndex + 1] /\
        UNCHANGED << NodeSet, Voting, Active, LastApplied, NextIndex, MatchIndex, HBElapsed, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived >>

LogDelete ==
    \E j \in NodeSet :
      PendingDelete[j] > 0 /\ PendingDelete[j] > CommitIndex[j] /\
      Log' = [Log EXCEPT ![j] = DropFrom(j, PendingDelete[j])] /\
      PendingDelete' = [PendingDelete EXCEPT ![j] = 0] /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived >>

RecvAppendEntriesResponse ==
    \E m \in Messages :
      m.mtype = "AppendEntriesResp" /\
      LET l == m.dst IN
      l \in NodeSet /\ Role[l] = "LEADER" /\
      Messages' = Messages \ {m} /\
      IF m.term > CurrentTerm[l]
      THEN /\ CurrentTerm' = [CurrentTerm EXCEPT ![l] = m.term]
           /\ Role' = [Role EXCEPT ![l] = "FOLLOWER"]
           /\ VotedFor' = [VotedFor EXCEPT ![l] = None]
           /\ LeaderId' = [LeaderId EXCEPT ![l] = None]
           /\ UNCHANGED << NodeSet, Voting, Active, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>
      ELSE /\ CurrentTerm' = CurrentTerm
           /\ Role' = Role
           /\ VotedFor' = VotedFor
           /\ LeaderId' = LeaderId
           /\ MatchIndex' = IF m.success
                            THEN [MatchIndex EXCEPT ![l] = [MatchIndex[l] EXCEPT ![m.src] = MaxNat(@, m.currentIndex)]]
                            ELSE MatchIndex
           /\ NextIndex' = IF m.success
                           THEN [NextIndex EXCEPT ![l] = [NextIndex[l] EXCEPT ![m.src] = MaxNat(@, m.currentIndex + 1)]]
                           ELSE [NextIndex EXCEPT ![l] = [NextIndex[l] EXCEPT ![m.src] = MaxNat(1, @ - 1)]]
           /\ UNCHANGED << NodeSet, Voting, Active, Log, CommitIndex, LastApplied, ElectionElapsed, ElectionDeadline, HBElapsed, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

LogCommit ==
    \E l \in NodeSet :
      Role[l] = "LEADER" /\
      \E idx \in Nat :
        idx > CommitIndex[l] /\ idx <= LastLogIndex(l) /\
        GetTermAt(l, idx) = CurrentTerm[l] /\
        Cardinality({ v \in Voters : v = l \/ MatchIndex[l][v] >= idx }) >= (Cardinality(Voters) \div 2) + 1 /\
        CommitIndex' = [CommitIndex EXCEPT ![l] = idx] /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, Log, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

LogAppend ==
    \E l \in NodeSet :
      Role[l] = "LEADER" /\
      \E e \in Entry :
        e.etype = "Data" /\ e.term = CurrentTerm[l] /\ e.node = None /\
        Log' = [Log EXCEPT ![l] = @ \o << e >>] /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

AddNode ==
    \E l \in NodeSet, x \in NODE_IDS :
      Role[l] = "LEADER" /\ x \notin NodeSet /\
      LET e == [term |-> CurrentTerm[l], etype |-> "AddNode", node |-> x] IN
      Log' = [Log EXCEPT ![l] = @ \o << e >>] /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

RemoveNode ==
    \E l \in NodeSet, x \in NodeSet :
      Role[l] = "LEADER" /\ x # l /\
      LET e == [term |-> CurrentTerm[l], etype |-> "RemoveNode", node |-> x] IN
      Log' = [Log EXCEPT ![l] = @ \o << e >>] /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

ApplyConfigChange ==
    \E n \in NodeSet :
      LastApplied[n] < CommitIndex[n] /\
      LET idx == LastApplied[n] + 1 IN
      idx <= LastLogIndex(n) /\
      LET pos == IndexToPos(n, idx) IN
      LET e == Log[n][pos] IN
      /\ (IF e.etype = "AddNode"
         THEN /\ NodeSet' = NodeSet \cup {e.node}
              /\ Active' = [Active EXCEPT ![e.node] = TRUE]
              /\ Voting' = [Voting EXCEPT ![e.node] = TRUE]
         ELSE IF e.etype = "AddNonVoting"
         THEN /\ NodeSet' = NodeSet \cup {e.node}
              /\ Active' = [Active EXCEPT ![e.node] = TRUE]
              /\ Voting' = [Voting EXCEPT ![e.node] = FALSE]
         ELSE IF e.etype = "RemoveNode"
         THEN /\ NodeSet' = NodeSet \ {e.node}
              /\ Active' = [Active EXCEPT ![e.node] = FALSE]
              /\ Voting' = [Voting EXCEPT ![e.node] = FALSE]
         ELSE /\ UNCHANGED << NodeSet, Active, Voting >>)
      /\ LastApplied' = [LastApplied EXCEPT ![n] = @ + 1] /\
      UNCHANGED << Role, CurrentTerm, VotedFor, LeaderId, Log, CommitIndex, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

SnapshotBegin ==
    \E n \in NodeSet :
      ~SnapshotInProgress[n] /\ LastApplied[n] > SnapLastIndex[n] /\
      SnapshotInProgress' = [SnapshotInProgress EXCEPT ![n] = TRUE] /\
      NextSnapshotIndex' = [NextSnapshotIndex EXCEPT ![n] = LastApplied[n]] /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, PreVotesReceived, VotesReceived, PendingDelete >>

SnapshotEnd ==
    \E n \in NodeSet :
      SnapshotInProgress[n] /\ NextSnapshotIndex[n] >= SnapLastIndex[n] /\
      LET newBase == NextSnapshotIndex[n] IN
      LET dropCount == newBase - SnapLastIndex[n] IN
      SnapLastIndex' = [SnapLastIndex EXCEPT ![n] = newBase] /\
      SnapLastTerm' = [SnapLastTerm EXCEPT ![n] =
          IF dropCount = 0 THEN SnapLastTerm[n]
          ELSE GetTermAt(n, newBase)] /\
      Log' = [Log EXCEPT ![n] =
          IF dropCount = 0 THEN @
          ELSE SubSeq(@, dropCount + 1, Len(@)) ] /\
      SnapshotInProgress' = [SnapshotInProgress EXCEPT ![n] = FALSE] /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, HBElapsed, Messages, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

PeriodicElectionTimeout ==
    \E n \in NodeSet :
      Role[n] # "LEADER" /\
      ElectionElapsed' = [ElectionElapsed EXCEPT ![n] = @ + 1] /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionDeadline, HBElapsed, Messages, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

PeriodicHeartbeat ==
    \E l \in NodeSet, f \in NodeSet :
      Role[l] = "LEADER" /\ l # f /\ Active[f] /\ HBElapsed[l] >= HEARTBEAT_TIMEOUT /\
      Messages' = Messages \cup
        { [mtype |-> "AppendEntries",
           term |-> CurrentTerm[l],
           leaderId |-> l,
           src |-> l,
           dst |-> f,
           prevLogIndex |-> LastLogIndex(l),
           prevLogTerm |-> LastLogTerm(l),
           leaderCommit |-> CommitIndex[l],
           entries |-> << >> ] } /\
      HBElapsed' = [HBElapsed EXCEPT ![l] = 0] /\
      UNCHANGED << NodeSet, Voting, Active, Role, CurrentTerm, VotedFor, LeaderId, Log, CommitIndex, LastApplied, NextIndex, MatchIndex, ElectionElapsed, ElectionDeadline, SnapLastIndex, SnapLastTerm, SnapshotInProgress, NextSnapshotIndex, PreVotesReceived, VotesReceived, PendingDelete >>

Next ==
    (\E n \in NodeSet : BecomeFollower(n))
    \/ (\E n \in NodeSet : BecomePreCandidate(n))
    \/ (\E n \in NodeSet : BecomeCandidate(n))
    \/ (\E n \in NodeSet : BecomeLeader(n))
    \/ RecvRequestVote
    \/ RecvRequestVoteResponse
    \/ RecvAppendEntries
    \/ RecvAppendEntriesResponse
    \/ SendAppendEntries
    \/ SendHeartbeat
    \/ (\E n \in NodeSet : ElectionStart(n))
    \/ (\E n \in NodeSet : ElectionTimeout(n))
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

Spec == Init /\ [][Next]_vars

====