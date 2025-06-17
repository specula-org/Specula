---- MODULE etcd ----
EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals

CONSTANTS
    \* 节点集合
    Nodes,
    \* 消息类型
    MsgVote,           \* 投票请求消息
    MsgPreVote,        \* 预投票请求消息
    MsgApp,            \* 日志追加消息
    MsgHeartbeat,      \* 心跳消息
    MsgSnap,           \* 快照消息
    MsgPreVoteResp,    \* 预投票响应消息
    MsgVoteResp,       \* 投票响应消息
    MsgAppResp,        \* 日志追加响应消息
    MsgHeartbeatResp,  \* 心跳响应消息
    MsgSnapResp,       \* 快照响应消息
    MsgTimeoutNow,     \* 超时消息
    MsgProp,           \* 提议消息
    MsgReadIndex,      \* 读取索引消息  
    MsgStorageAppendResp,
    MsgStorageApplyResp,
    MsgStorageAppend,
    MsgHup,
    MsgTransferLeader,
    MsgForgetLeader,
    MsgBeat,
    EntryConfChange, 
    EntryConfChangeV2,

    \* 节点状态
    StateLeader,       \* Leader状态
    StateFollower,     \* Follower状态
    StateCandidate,    \* Candidate状态
    StatePreCandidate, \* PreCandidate状态
    StateLearner,      \* Learner状态
    
    stepCandidate,     \* Candidate步骤
    stepFollower,      \* Follower步骤
    stepLeader,        \* Leader步骤
    stepPreCandidate,  \* PreCandidate步骤
    \* 其他常量
    None,              \* 空值
    QuorumWon,         \* 获得多数派
    QuorumPending,     \* 等待多数派
    QuorumLost,        \* 失去多数派
    
    \* 配置参数
    MaxInflightMsgs,   \* 最大未确认消息数
    ElectionTimeout,   \* 选举超时时间
    HeartbeatTimeout   \* 心跳超时时间

VARIABLES
    \* 节点状态相关变量
    id,               \* 节点ID
    state,          \* 节点状态
    term,           \* 当前任期
    Vote,           \* 投票给谁
    lead,           \* leader节点
    step,

    \* 日志相关变量
    raftLog,              \* 日志
    raftLog_committed,    \* 已提交的日志索引
    raftLog_lastIndex,    \* 最后一条日志的索引
    appliedTo,            \* 已应用的日志索引
    messages,             \* 消息集合
    msgsAfterAppend,

    \* 选举相关变量
    electionElapsed,      \* 选举计时器
    electionTimeout,      \* 选举超时时间
    campaignType,         \* 竞选类型
    trk_Votes,           \* 投票追踪
    pendingConfIndex,     \* 等待多数派索引
    
    stableIndex,
    stableTerm,
    snapshot,

    \* 其他变量

    uncommittedSize,     \* 未提交的数据大小
    maxUncommittedSize,   \* 最大未提交数据大小
    trk_Progress,
    active_nodes,
    heartbeatElapsed,
    leadTransferee

node_vars == <<id, state, term, Vote, lead, step>>
log_vars == <<raftLog, raftLog_committed, raftLog_lastIndex, appliedTo, messages, msgsAfterAppend>>
election_vars == <<electionElapsed, electionTimeout, campaignType, trk_Votes, pendingConfIndex>>
stable_vars == <<stableIndex, stableTerm>>
snapshot_vars == <<snapshot>>
other_vars == <<uncommittedSize, maxUncommittedSize, trk_Progress, active_nodes, heartbeatElapsed, leadTransferee>>

vars == <<node_vars, log_vars, election_vars, stable_vars, snapshot_vars, other_vars>>

Min(x, y) == IF x > y THEN y ELSE x
Max(x, y) == IF x > y THEN x ELSE y

Poll(r, idd, t, v) ==
    /\ LET granted == Cardinality({ voter \in DOMAIN trk_Votes[r] : trk_Votes'[r][voter] })  rejected == Cardinality({ voter \in DOMAIN trk_Votes[r] : ~trk_Votes'[r][voter] }) IN 
        /\ IF granted > (Cardinality(DOMAIN trk_Votes'[r]) \div 2) THEN QuorumWon 
            ELSE /\ IF rejected > (Cardinality(DOMAIN trk_Votes[r]) \div 2) THEN QuorumLost
                    ELSE QuorumPending

Promotable(r) ==
    /\ trk_Progress[r][id[r]] /= FALSE
    /\ state[r] /= StateLearner

Send(r, m) ==
    LET msg == [From |-> IF m.From = None THEN id[r] ELSE m.From] IN
        /\ IF msg.Type \in {MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp} THEN
            /\ msg.Term /= 0
            ELSE 
            /\ msg.Term = 0
            /\ IF ~(msg.Type \in {MsgProp, MsgReadIndex}) THEN
                /\ m.Term = term[r]
                ELSE UNCHANGED <<>>
        /\ IF msg.Type \in {MsgAppResp, MsgVoteResp, MsgPreVoteResp} THEN 
            /\ msgsAfterAppend' = Append(msgsAfterAppend, msg)
            ELSE 
            /\ m.To /= raftLog
            /\ messages' = Append(messages, msg)

HandleAppendEntries(r, m) ==
    /\ LET a == m.entries IN
        /\ IF a[Len(a)].Index < raftLog_committed[r] THEN 
           /\ messages' = messages \cup {[Type |-> "MsgAppResp", To |-> m.From, Index |-> raftLog_committed[r]]}
           ELSE 
           /\ LET mlastIndex == IF a[Len(a)].Term = raftLog[r][Len(a)].Term THEN a[Len(a)].Index ELSE 0 IN 
               /\ IF a[Len(a)].Term = raftLog[r][Len(a)].Term THEN 
                   /\ \A i \in DOMAIN a:
                       /\ raftLog' = [raftLog EXCEPT ![r] = [@ EXCEPT ![a[i].Index] = a[i]]]
                   /\ LET hintIndex == Min(a[Len(a)].Index, raftLog[r][Len(raftLog[r])].Index)
                        hintTerm == raftLog[r][hintIndex].Term
                    IN
                        /\ messages' = messages \cup {[Type |-> "MsgAppResp", To |-> m.From, Index |-> m.Index, reject |-> TRUE, rejectHint |-> hintIndex, logTerm |-> hintTerm]}
                   ELSE
                   /\ messages' = messages \cup {[Type |-> "MsgAppResp", To |-> m.From, Index |-> mlastIndex]}
                   
HandleHeartbeat(r, m) ==
    /\ raftLog_committed' = [raftLog_committed EXCEPT ![r] = raftLog_committed[m]]
    /\ messages' = messages \cup {[From |-> r, To |-> m.From, Type |-> MsgHeartbeatResp, Context |-> m.Context]}

HandleSnapshot(r, m) ==
    LET s == IF m.Snap /= None THEN m.Snap ELSE None
        sindex == s.Metadata.Index
        sterm == s.Metadata.Term
    IN
        /\ IF sindex > raftLog_committed[r] /\ sterm >= term[r] THEN
            /\ term' = [term EXCEPT ![r] = sterm]
            /\ raftLog_committed' = [raftLog_committed EXCEPT ![r] = sindex]
            /\ raftLog_lastIndex' = [raftLog_lastIndex EXCEPT ![r] = sindex]
            /\ messages' = messages \cup {[type |-> "MsgAppResp", to |-> m.From, from |-> r, index |-> sindex]}
            ELSE 
            /\ messages' = messages \cup {[type |-> "MsgAppResp", to |-> m.From, from |-> r, index |-> raftLog_committed[r]]}
            /\ UNCHANGED <<term, raftLog_committed, raftLog_lastIndex>>

BcastAppend(r) ==
    messages' = messages \cup { [type |-> "Append", from |-> r, to |-> idd] : idd \in { x \in (DOMAIN trk_Progress[r]) : x /= id[r] }}

BecomePreCandidate(r) ==
    /\ state[r] /= StateLeader \* 检查前置条件
    /\ step' = [step EXCEPT ![r] = stepPreCandidate]
    /\ trk_Votes' = [trk_Votes EXCEPT ![r] = [idd \in DOMAIN trk_Votes[r] |-> FALSE]] \* 重置投票
    /\ lead' = [lead EXCEPT ![r] = None]
    /\ state' = [state EXCEPT ![r] = StatePreCandidate]
    /\ UNCHANGED <<term, Vote>> \* 不改变term和vote

BecomeCandidate(r) ==
    /\ state[r] # StateLeader
    /\ step' = [step EXCEPT ![r] = stepCandidate]
    /\ term' = [term EXCEPT ![r] = term[r] + 1]
    /\ Vote' = [Vote EXCEPT ![r] = id[r]]
    /\ state' = [state EXCEPT ![r] = StateCandidate]

Campaign(r, t) ==
    LET voteMsg == IF t = "campaignPreElection" THEN "MsgPreVote" ELSE "MsgVote" IN
        /\ IF t = "campaignPreElection"
            THEN 
            /\ BecomePreCandidate(r)
            /\ term' = [r |-> term[r] + 1]
            ELSE 
            /\ BecomeCandidate(r)
            /\ term' = [r |-> term[r]]
        /\ LET ids == DOMAIN trk_Votes[r] IN
            /\ \A idd \in ids:
                IF idd = r.id THEN
                    /\ msgsAfterAppend' = Append(msgsAfterAppend, [To |-> idd, Term |-> term'[r], Type |-> voteMsg])
                    ELSE /\ Send(r, [To |-> id, Term |-> term'[r], Type |-> voteMsg'[r], Index |-> raftLog[r][Len(raftLog[r])].Index, LogTerm |-> raftLog[r][Len(raftLog[r])].Term])
        /\ UNCHANGED <<MaxInflightMsgs>>

StepCandidate(r, m) ==
    LET myVoteRespType == IF state[r] = "PreCandidate" THEN "MsgPreVoteResp" ELSE "MsgVoteResp"
    IN
        /\ CASE m.type = "MsgProp" -> 
                UNCHANGED <<state, term>>
            [] m.type = "MsgApp" ->
                /\ state' = [state EXCEPT ![r] = "Follower"]
                /\ lead' = [lead EXCEPT ![r] = m.from]
                /\ HandleAppendEntries(r, m)
            [] m.type = "MsgHeartbeat" ->
                /\ state' = [state EXCEPT ![r] = "Follower"]
                /\ lead' = [lead EXCEPT ![r] = m.from]
                /\ HandleHeartbeat(r, m)
            [] m.type = "MsgSnap" ->
                /\ state' = [state EXCEPT ![r] = "Follower"]
                /\ lead' = [lead EXCEPT ![r] = m.from]
                /\ HandleSnapshot(r, m)
            [] m.type = myVoteRespType ->
                /\ trk_Votes' = [trk_Votes EXCEPT ![r][id] = ~m.reject]
                /\ LET PollResult == Poll(r, m.from, m.type, ~m.reject) IN
                    /\ CASE PollResult.result = "VoteWon" ->
                            IF state[r] = "PreCandidate"
                                THEN /\ Campaign(r, "campaignPreElection")
                                ELSE /\ state' = [state EXCEPT ![r] = "Leader"]
                                /\ BcastAppend(r)
                        [] PollResult.result = "VoteLost" ->
                            /\ state' = [state EXCEPT ![r] = "Follower"]
                            /\ lead' = [lead EXCEPT ![r] = "None"]
                            /\ term' = [term EXCEPT ![r] = term[r]]
                        [] OTHER -> UNCHANGED <<state, term>>
            [] m.type = "MsgTimeoutNow" ->
                UNCHANGED <<state, term>>
            [] OTHER -> UNCHANGED <<state, term>>
        /\ UNCHANGED MaxInflightMsgs

BecomeFollower(r, currentTerm, currentLead) ==
    /\ step' = [step EXCEPT ![r] = stepFollower]
    /\ term' = [term EXCEPT ![r] = currentTerm]
    /\ lead' = [lead EXCEPT ![r] = currentLead]
    /\ state' = [state EXCEPT ![r] = StateFollower]

AppliedTo(index, r) ==
    /\ appliedTo' = [appliedTo EXCEPT ![r] = Max(index, appliedTo[r])]
    /\ IF appliedTo'[r] >= pendingConfIndex[r] /\ state[r] = "StateLeader"
        THEN
        /\ messages' = Append(messages, [Type |-> "ConfChangeV2", Term |-> term[r], From |-> r])
        ELSE
        /\ messages' = messages

ReduceUncommittedSize(r, s) ==
    IF s > uncommittedSize[r]
        THEN uncommittedSize' = [uncommittedSize EXCEPT ![r] = 0]
        ELSE uncommittedSize' = [uncommittedSize EXCEPT ![r] = uncommittedSize[r] - s]

RaftLog_isUpToDate(r, candLastID) ==
    /\ candLastID.Index > Len(raftLog[r])
    /\ candLastID.Term >= raftLog[r][Len(raftLog[r])].Term

HasUnappliedConfChanges(r) ==
    /\ appliedTo[r] < pendingConfIndex[r]
    /\ \E idx \in (appliedTo[r] + 1)..pendingConfIndex[r] :
        /\ raftLog[r][idx].Type \in {EntryConfChangeV2, EntryConfChange}

Hup(r, t) ==
    /\ state[r] # "Leader"
    /\ Promotable(r)
    /\ ~HasUnappliedConfChanges(r)
    /\ term' = [term EXCEPT ![r] = @ + 1]
    /\ state' = [state EXCEPT ![r] = "Candidate"]

SendHeartbeat(r, to) ==
    /\ Send(r, [Type |-> "MsgHeartbeat", To |-> to, Commit |-> pendingConfIndex[r], Context |-> None])

BcastHeartbeatWithCtx(r, ctx) ==
    /\ \A idd \in Nodes:
        /\ IF idd /= r
            THEN SendHeartbeat(r, idd)
            ELSE UNCHANGED <<>>
\* 发送心跳
BcastHeartbeat(r) ==
       /\ BcastHeartbeatWithCtx(r, None)

IncreaseUncommittedSize(r, s) ==
    \/ /\ uncommittedSize[r] > 0
       /\ s > 0
       /\ uncommittedSize[r] + s > maxUncommittedSize[r]
       /\ uncommittedSize' = uncommittedSize
       /\ maxUncommittedSize' = maxUncommittedSize
    \/ /\ uncommittedSize' = [uncommittedSize EXCEPT ![r] = @ + s]
       /\ maxUncommittedSize' = maxUncommittedSize
       /\ \/ uncommittedSize[r] = 0
          \/ s = 0
          \/ uncommittedSize[r] + s <= maxUncommittedSize[r]


AppendEntry(r, es) ==
    LET li == Len(raftLog[r])
        modified_es == [i \in 1..Len(es) |-> [Term |-> term[r], Index |-> li + i]]
    IN
        /\ IncreaseUncommittedSize(r, Len(modified_es))
        /\ raftLog' = [raftLog EXCEPT ![r] = Append(@[r], modified_es)]
        /\ messages' = messages \cup {[To |-> id[r], Type |-> "MsgAppResp", Index |-> li + Len(modified_es)]}


MaybeSendAppend(r, to, sendIfEmpty) ==
    /\ LET prevIndex == Len(raftLog[r]) preTerm == raftLog[r][prevIndex].Term ents == raftLog[r] IN
        /\ Send(r, [Type |-> "MsgApp", To |-> to, Index |-> prevIndex, LogTerm |-> preTerm, Entries |-> ents, Commit |-> pendingConfIndex[r]])

SendAppend(r, to) ==
    /\ MaybeSendAppend(r, to, TRUE)



MaybeCommit(r, ents) ==
    /\ raftLog[r][pendingConfIndex[r]].Term = term[r]
    /\ ents.Term /= 0
    /\ ents.Index > pendingConfIndex[r]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![r] = ents.Index]

StepLeader(r, m) ==
    /\ CASE m.Type = MsgBeat ->
            /\ BcastHeartbeat(r)
        [] m.Type = MsgProp ->
            /\ Len(m.entries) > 0
            /\ leadTransferee[r] = None
            /\ AppendEntry(r, m.entries)
            /\ BcastAppend(r)
        [] m.Type = MsgForgetLeader ->
            /\ UNCHANGED <<state, term>>
        [] m.Type = MsgAppResp ->
            /\ IF m.reject
               THEN /\ LET nextProbeIdx == m.RejectHint IN 
                /\ SendAppend(r, [Type |-> MsgApp, To |-> m.From])
               ELSE 
               /\ IF MaybeCommit(r, m.entries)
                    THEN /\ BcastAppend(r)
                    ELSE /\ IF m.From # r
                        THEN /\ SendAppend(r, [Type |-> MsgApp, To |-> m.From])
                        ELSE /\ UNCHANGED <<>>
                /\ IF r /= m.From THEN 
                    /\ MaybeSendAppend(r, m.From, FALSE)
                    ELSE UNCHANGED <<>>
                /\ IF /\ m.From = leadTransferee[r] /\ m.Index = raftLog_lastIndex[r]
                    THEN /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
                    ELSE /\ UNCHANGED <<>>
                /\ IF m.From = leadTransferee[r]
                    THEN /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
                    ELSE /\ UNCHANGED <<>>
        [] m.Type = MsgHeartbeatResp ->
            /\ SendAppend(r, m.From)
        [] m.Type = MsgTransferLeader ->
            /\ IF /\ m.From # r
               THEN 
               /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
               /\ leadTransferee' = [leadTransferee EXCEPT ![r] = m.From]
               /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
               ELSE /\ UNCHANGED <<>>
        [] OTHER -> UNCHANGED <<state, term>>



StepFollower(r, m) ==
    \/ /\ m.Type = MsgProp
       /\ /\ lead[r] /= None
          /\ Send(r, m)
    \/ /\ m.Type \in {MsgApp, MsgHeartbeat, MsgSnap}
       /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
       /\ lead' = [lead EXCEPT ![r] = m.From]
       /\ HandleAppendEntries(r, m)
    \/ /\ m.Type = MsgTransferLeader
       /\ /\ lead[r] /= None
          /\ m.To = lead[r]
          /\ Send(r, m)
    \/ /\ m.Type = MsgForgetLeader
       /\ lead[r] /= None
       /\ lead' = [lead EXCEPT ![r] = None]
    \/ /\ m.Type = MsgTimeoutNow
       /\ Hup(r, "campaignTransfer")
    \/ /\ m.Type = MsgReadIndex
       /\ lead[r] /= None
       /\ m.To = lead[r]
       /\ Send(r, m)


Step(r, m) ==
    /\ IF m.Term = 0 THEN 
       /\ UNCHANGED <<state, term, lead, step>>
       ELSE 
       \/ /\ m.Term > term[r]
          /\ IF m.Type \in {MsgApp, MsgHeartbeat, MsgSnap}
             THEN /\ BecomeFollower(r, m.Term, m.From)
             ELSE /\ IF ~(m.Type \in {MsgVote, MsgPreVote})
                    THEN /\ BecomeFollower(r, m.Term, m.From)
                    ELSE UNCHANGED <<state, term, lead, step>>
       \/ /\ m.Term < term[r]
          /\ IF m.type \in {MsgApp, MsgHeartbeat} THEN
            /\ Send(r, [Type |-> MsgAppResp, To |-> m.from]) \* 返回拒绝响应
            ELSE IF m.type = MsgPreVote
                THEN Send(r, [Type |-> MsgPreVoteResp, To |-> m.from, reject |-> TRUE])
                ELSE IF m.type = MsgStorageAppendResp
                    THEN IF m.Snapshot /= None THEN
                        /\ AppliedTo(m.Snapshot.Metadata.Index, r)
                        ELSE
                        /\ UNCHANGED <<>>
                    ELSE UNCHANGED <<>>
    /\ CASE m.type = MsgHup ->
            /\ Hup(r, "CampaignPreElection")
        [] m.type = MsgStorageAppend ->
            /\ IF m.Index /= 0 THEN 
                /\ stableIndex' = [stableIndex EXCEPT ![r] = m.Index]
                /\ stableTerm' = [stableTerm EXCEPT ![r] = m.Term]
                ELSE
                /\ IF m.Snapshot /= None THEN
                    /\ stableIndex' = [stableIndex EXCEPT ![r] = m.Snapshot.Index]
                    /\ stableTerm' = [stableTerm EXCEPT ![r] = m.Snapshot.Term]
                    ELSE
                    /\ UNCHANGED <<stableIndex, stableTerm>>
        [] m.type = MsgStorageApplyResp ->
            /\ IF m.entries /= <<>> THEN
                /\ AppliedTo(Len(m.entries), r)
                /\ ReduceUncommittedSize(r, Len(m.entries))
                ELSE 
                /\ UNCHANGED <<>>
        [] m.type \in {MsgVote, MsgPreVote} ->
            /\ LET canVote == IF Vote[r] = m.From THEN TRUE
                                ELSE /\ IF Vote[r] = None /\ lead[r] = None THEN TRUE
                                    ELSE /\ IF m.Type = "MsgPreVote" /\ m.Term > term[r] THEN TRUE
                                        ELSE FALSE  
                   lastID == [Term |-> raftLog[r][Len(raftLog[r])].Term, Index |-> raftLog[r][Len(raftLog[r])].Index]
                   candLastID == [Term |-> m.LogTerm, Index |-> m.Index]
            IN
               \/ /\ canVote 
                  /\ RaftLog_isUpToDate(r, candLastID)
                  /\ IF m.Type = "MsgVote"
                     THEN 
                     /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
                     /\ Vote' = [Vote EXCEPT ![r] = m.From]
                     ELSE /\ UNCHANGED <<electionElapsed, Vote>>
                  /\ Send(r, [Type |-> IF m.Type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp", To |-> m.From, Term |-> m.Term, reject |-> FALSE])
               \/ /\ ~canVote \/ ~RaftLog_isUpToDate(r, candLastID)
                  /\ Send(r, [Type |-> IF m.Type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp", To |-> m.From, Term |-> term[r], reject |-> TRUE])
                  /\ UNCHANGED <<electionElapsed, Vote>>
        [] OTHER ->
            /\ CASE state[r] = "Candidate" ->
                    /\ StepCandidate(r, m)
                [] state[r] = "Follower" ->
                    /\ StepFollower(r, m)
                [] state[r] = "Leader" ->
                    /\ StepLeader(r, m)

\* 超时选举
TickElection(r) ==
    /\ IF Promotable(r) /\ electionElapsed[r] >= electionTimeout[r] THEN 
        /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
        /\ Step(r, [Type |-> "MsgHup", From |-> id[r]])
        ELSE 
        /\ electionElapsed' = [electionElapsed EXCEPT ![r] = @ + 1]

IsEmptySnap(s) ==
    /\ s.Metadata.Index = 0
    /\ s.Metadata.Term = 0

MaybeSendSnapshot(r, to, pr) ==
    /\ LET sindex == snapshot[r].Index  sterm == snapshot[r].Term IN
        /\ ~IsEmptySnap(snapshot[r]) \* Critical assertion
        /\ Send(r, [Type |-> "MsgSnap", To |-> to, Snapshot |-> snapshot[r]])



BecomeLeader(r) ==
    /\ state[r] /= StateFollower
    /\ step' = [step EXCEPT ![r] = stepLeader]
    /\ Vote' = [Vote EXCEPT ![r] = None]
    /\ lead' = [lead EXCEPT ![r] = id[r]]
    /\ state' = [state EXCEPT ![r] = StateLeader]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![r] = raftLog_lastIndex[r]]
    /\ raftLog_lastIndex' = [raftLog_lastIndex EXCEPT ![r] = raftLog_lastIndex[r] + 1]
    /\ raftLog' = [raftLog EXCEPT ![r] = Append(raftLog[r], [Term |-> term[r], Data |-> None])]

checkQuorum == 
    /\ Cardinality(active_nodes) >= Cardinality(Nodes) \div 2 + 1

TickHeartbeat(r) ==
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![r] = @ + 1]
    /\ electionElapsed' = [electionElapsed EXCEPT ![r] = @ + 1]
    /\ IF electionElapsed[r] >= electionTimeout[r]
        THEN 
        /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
        /\ IF state[r] = StateLeader /\ leadTransferee[r] /= None THEN 
            /\ leadTransferee' = [leadTransferee EXCEPT ![r] = None]
            ELSE
            /\ UNCHANGED leadTransferee
        ELSE 
        /\ UNCHANGED electionElapsed
        /\ UNCHANGED leadTransferee
    /\ IF state[r] = StateLeader
        THEN /\ IF heartbeatElapsed[r] >= HeartbeatTimeout
                 THEN /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![r] = 0]
                      /\ Step(r, [From |-> id[r], Type |-> MsgBeat])
                 ELSE /\ UNCHANGED heartbeatElapsed
        ELSE /\ UNCHANGED heartbeatElapsed




AbortLeaderTransfer(r) ==
    /\ leadTransferee' = [leadTransferee EXCEPT ![r] = None]


AppliedSnap(r, snap) ==
    /\ snap.Index > snapshot[r].Index
    /\ snapshot[r] = snap

LoadState(r, state_Commit, state_Term, state_Vote) ==
    /\ state_Commit >= raftLog_committed[r]
    /\ state_Commit <= raftLog_lastIndex[r]
    /\ raftLog_committed' = [raftLog_committed EXCEPT ![r] = state_Commit]
    /\ term' = [term EXCEPT ![r] = state_Term]
    /\ Vote' = [Vote EXCEPT ![r] = state_Vote]

Next == 
    \/ /\ \E n \in Nodes: TickElection(n)
       /\ UNCHANGED <<node_vars, log_vars, stable_vars, snapshot_vars, other_vars, electionTimeout, campaignType, trk_Votes, pendingConfIndex>>

Init ==
    /\ id = [n \in Nodes |-> n]  \* 每个节点的ID就是节点本身
    /\ state = [n \in Nodes |-> StateFollower]  \* 所有节点初始为Follower
    /\ term = [n \in Nodes |-> 0]  \* 初始任期为0
    /\ Vote = [n \in Nodes |-> None]  \* 初始未投票给任何节点
    /\ lead = [n \in Nodes |-> None]  \* 初始没有leader
    /\ step = [n \in Nodes |-> stepFollower]  \* 初始步骤为Follower
    
    \* 日志相关初始化
    /\ raftLog = [n \in Nodes |-> <<>>]  \* 空日志
    /\ raftLog_committed = [n \in Nodes |-> 0]  \* 已提交索引为0
    /\ raftLog_lastIndex = [n \in Nodes |-> 0]  \* 最后日志索引为0
    /\ appliedTo = [n \in Nodes |-> 0]  \* 已应用索引为0
    /\ messages = {}  \* 空消息集
    /\ msgsAfterAppend = {}  \* 空追加后消息集
    
    \* 选举相关初始化
    /\ electionElapsed = [n \in Nodes |-> 0]  \* 选举计时器初始为0
    /\ electionTimeout = [n \in Nodes |-> ElectionTimeout]  \* 选举超时时间
    /\ campaignType = [n \in Nodes |-> None]  \* 初始无竞选类型
    /\ trk_Votes = [n \in Nodes |-> [m \in Nodes |-> FALSE]]  \* 空投票追踪
    /\ pendingConfIndex = [n \in Nodes |-> 0]  \* 等待多数派索引为0
    
    /\ stableIndex = [n \in Nodes |-> 0]  \* 稳定索引为0
    /\ stableTerm = [n \in Nodes |-> 0]  \* 稳定任期为0
    /\ snapshot = [n \in Nodes |-> None]  \* 初始无快照
    
    \* 其他变量初始化
    /\ uncommittedSize = [n \in Nodes |-> 0]  \* 未提交大小为0
    /\ maxUncommittedSize = [n \in Nodes |-> 0]  \* 最大未提交大小为0
    /\ trk_Progress = [n \in Nodes |-> [m \in Nodes |-> TRUE]]  \* 空进度追踪
    /\ active_nodes = [n \in Nodes |-> {}]  \* 空活跃节点集
    /\ heartbeatElapsed = [n \in Nodes |-> 0]  \* 心跳计时器为0
    /\ leadTransferee = [n \in Nodes |-> None]  \* 初始无leader转移目标

Spec == Init /\ [][Next]_(vars)
====