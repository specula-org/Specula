Send(r, m) ==
    LET msg == [From |-> IF m.From = None THEN id[r] ELSE m.From] IN
        /\ IF msg.Type \in {MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp} THEN
            /\ msg.Term /= 0
            ELSE
            /\ msg.Term = 0
            /\ IF ~(msg.Type \in {MsgProp, MsgReadIndex}) THEN
                /\ m.Term = term[r]
                ELSE
                UNCHANGED <<>>
        /\ IF msg.Type \in {MsgAppResp, MsgVoteResp, MsgPreVoteResp} THEN
            /\ msgsAfterAppend' = Append(msgsAfterAppend, msg)
            /\ UNCHANGED <<messages>>
            ELSE
            /\ m.To /= raftLog
            /\ messages' = Append(messages, msg)
            /\ UNCHANGED <<msgsAfterAppend>>
SendHeartbeat(r, to) ==
    /\ Send(r, [Type |-> "MsgHeartbeat", To |-> to, Commit |-> pendingConfIndex[r], Context |-> None])
MaybeSendAppend(r, to, sendIfEmpty) ==
    /\ LET prevIndex == Len(raftLog[r])
        preTerm == raftLog[r][prevIndex].Term
        ents == raftLog[r] IN
        /\ Send(r, [Type |-> "MsgApp", To |-> to, Index |-> prevIndex, LogTerm |-> preTerm, Entries |-> ents, Commit |-> pendingConfIndex[r]])
IncreaseUncommittedSize(r, s) ==
    \//\ uncommittedSize[r] > 0
        /\ s > 0
        /\ uncommittedSize[r] + s > maxUncommittedSize[r]
        /\ uncommittedSize' = uncommittedSize
        /\ maxUncommittedSize' = maxUncommittedSize
    \//\ uncommittedSize' = [uncommittedSize EXCEPT ![r] = @ + s]
        /\ maxUncommittedSize' = maxUncommittedSize
        /\ \/uncommittedSize'[r] = 0
            \/s = 0
            \/uncommittedSize'[r] + s <= maxUncommittedSize'[r]
BcastHeartbeatWithCtx(r, ctx) ==
    /\ \A idd \in Nodes:
        /\ IF idd /= r
            THEN SendHeartbeat(r, idd)
            ELSE UNCHANGED <<>>

HasUnappliedConfChanges(r) ==
    /\ appliedTo[r] < pendingConfIndex[r]
    /\ \E idx \in (appliedTo[r] + 1)..pendingConfIndex[r] :
        /\ raftLog[r][idx].Type \in {EntryConfChangeV2, EntryConfChange}


Promotable(r) ==
    /\ trk_Progress[r][id[r]] /= FALSE
    /\ state[r] /= StateLearner
Min(x, y) ==
    IF x > y THEN
        y
        ELSE
        x
BecomeCandidate(r) ==
    /\ state[r] # StateLeader
    /\ step' = [step EXCEPT ![r] = stepCandidate]
    /\ term' = [term EXCEPT ![r] = term[r] + 1]
    /\ Vote' = [Vote EXCEPT ![r] = id[r]]
    /\ state' = [state EXCEPT ![r] = StateCandidate]
BecomePreCandidate(r) ==
    /\ state[r] /= StateLeader
    /\ step' = [step EXCEPT ![r] = stepPreCandidate]
    /\ trk_Votes' = [trk_Votes EXCEPT ![r] = [idd \in DOMAIN trk_Votes[r] |-> FALSE]]
    /\ lead' = [lead EXCEPT ![r] = None]
    /\ state' = [state EXCEPT ![r] = StatePreCandidate]
    /\ UNCHANGED <<term, Vote>>
Max(x, y) ==
    IF x > y THEN
        x
        ELSE
        y
SendAppend(r, to) ==
    /\ MaybeSendAppend(r, to, TRUE)
BcastAppend(r) ==
    messages' = messages \cup { [type |-> "Append", from |-> r, to |-> idd] : idd \in { x \in (DOMAIN trk_Progress[r]) : x /= id[r] }}
MaybeCommit(r, ents) ==
    /\ raftLog[r][pendingConfIndex[r]].Term = term[r]
    /\ ents.Term /= 0
    /\ ents.Index > pendingConfIndex[r]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![r] = ents.Index]
AppendEntry(r, es) ==
    LET li == Len(raftLog[r])
        modified_es == [i \in 1..Len(es) |-> [Term |-> term[r], Index |-> li + i]] IN
        /\ IncreaseUncommittedSize(r, Len(modified_es))
        /\ raftLog' = [raftLog EXCEPT ![r] = Append(@[r], modified_es)]
        /\ messages' = messages \cup {[To |-> id[r], Type |-> "MsgAppResp", Index |-> li + Len(modified_es)]}
BcastHeartbeat(r) ==
    /\ BcastHeartbeatWithCtx(r, None)
Hup(r, t) ==
    /\ state[r] # "Leader"
    /\ Promotable(r)
    /\ ~HasUnappliedConfChanges(r)
    /\ term' = [term EXCEPT ![r] = @ + 1]
    /\ state' = [state EXCEPT ![r] = "Candidate"]
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
                        hintTerm == raftLog[r][hintIndex].Term IN
                        /\ messages' = messages \cup {[Type |-> "MsgAppResp", To |-> m.From, Index |-> m.Index, reject |-> TRUE, rejectHint |-> hintIndex, logTerm |-> hintTerm]}
                    ELSE
                    /\ messages' = messages \cup {[Type |-> "MsgAppResp", To |-> m.From, Index |-> mlastIndex]}
Campaign(r, t) ==
    LET voteMsg == IF t = "campaignPreElection" THEN "MsgPreVote" ELSE "MsgVote" IN
        /\ IF t = "campaignPreElection" THEN
            /\ BecomePreCandidate(r)
            /\ pc' = "Campaign_1"
            /\ info' = [args |-> <<r, t>>, temp |-> [voteMsg |-> voteMsg]]
            ELSE
            /\ BecomeCandidate(r)
            /\ pc' = "Campaign_2"
            /\ info' = [args |-> <<r, t>>, temp |-> [voteMsg |-> voteMsg]]
            /\ UNCHANGED <<trk_Votes, lead>>
Poll(r, idd, t, v) ==
    /\ LET granted == Cardinality({ voter \in DOMAIN trk_Votes[r] : trk_Votes'[r][voter] })
        rejected == Cardinality({ voter \in DOMAIN trk_Votes[r] : ~trk_Votes'[r][voter] }) IN
        /\ IF granted > (Cardinality(DOMAIN trk_Votes'[r]) \div 2) THEN
            QuorumWon
            ELSE
            /\ IF rejected > (Cardinality(DOMAIN trk_Votes'[r]) \div 2) THEN
                QuorumLost
                ELSE
                QuorumPending
HandleSnapshot(r, m) ==
    LET s == IF m.Snap /= None THEN m.Snap ELSE None
        sindex == s.Metadata.Index
        sterm == s.Metadata.Term IN
        /\ IF sindex > raftLog_committed[r] /\ sterm >= term[r] THEN
            /\ term' = [term EXCEPT ![r] = sterm]
            /\ raftLog_committed' = [raftLog_committed EXCEPT ![r] = sindex]
            /\ raftLog_lastIndex' = [raftLog_lastIndex EXCEPT ![r] = sindex]
            /\ messages' = messages \cup {[type |-> "MsgAppResp", to |-> m.From, from |-> r, index |-> sindex]}
            ELSE
            /\ messages' = messages \cup {[type |-> "MsgAppResp", to |-> m.From, from |-> r, index |-> raftLog_committed[r]]}
            /\ UNCHANGED <<term, raftLog_committed, raftLog_lastIndex>>
HandleHeartbeat(r, m) ==
    /\ raftLog_committed' = [raftLog_committed EXCEPT ![r] = raftLog_committed[m]]
    /\ messages' = messages \cup {[From |-> r, To |-> m.From, Type |-> MsgHeartbeatResp, Context |-> m.Context]}
AppliedTo(index, r) ==
    /\ appliedTo' = [appliedTo EXCEPT ![r] = Max(index, appliedTo[r])]
    /\ pc' = "AppliedTo_1"
    /\ info' = [args |-> <<index, r>>, temp |-> <<>>]
BecomeFollower(r, currentTerm, currentLead) ==
    /\ step' = [step EXCEPT ![r] = stepFollower]
    /\ term' = [term EXCEPT ![r] = currentTerm]
    /\ lead' = [lead EXCEPT ![r] = currentLead]
    /\ state' = [state EXCEPT ![r] = StateFollower]
StepLeader(r, m) ==
    /\ CASE m.Type = MsgBeat ->
            /\ BcastHeartbeat(r)
            /\ pc' = stack[Len(stack)].backsite
            /\ stack' = Tail(stack)
            /\ info' = stack[Len(stack)].info
            /\ UNCHANGED <<leadTransferee, maxUncommittedSize, raftLog, term, electionElapsed, state, pendingConfIndex, uncommittedSize>>
        [] m.Type = MsgProp ->
            /\ Len(m.entries) > 0
            /\ leadTransferee[r] = None
            /\ AppendEntry(r, m.entries)
            /\ pc' = "StepLeader_1"
            /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
            /\ UNCHANGED <<stack, leadTransferee, msgsAfterAppend, term, electionElapsed, state, pendingConfIndex>>
        [] m.Type = MsgForgetLeader ->
            /\ UNCHANGED <<state, term>>
            /\ pc' = stack[Len(stack)].backsite
            /\ stack' = Tail(stack)
            /\ info' = stack[Len(stack)].info
            /\ UNCHANGED <<leadTransferee, maxUncommittedSize, msgsAfterAppend, raftLog, messages, electionElapsed, pendingConfIndex, uncommittedSize>>
        [] m.Type = MsgAppResp ->
            /\ IF m.reject THEN
                /\ LET nextProbeIdx == m.RejectHint IN
                    /\ SendAppend(r, [Type |-> MsgApp, To |-> m.From])
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
                    /\ UNCHANGED <<leadTransferee, maxUncommittedSize, raftLog, term, electionElapsed, state, pendingConfIndex, uncommittedSize>>
                ELSE
                /\ IF MaybeCommit(r, m.entries) THEN
                    /\ BcastAppend(r)
                    /\ UNCHANGED <<msgsAfterAppend>>
                    ELSE
                    /\ IF m.From # r THEN
                        /\ SendAppend(r, [Type |-> MsgApp, To |-> m.From])
                        ELSE
                        /\ UNCHANGED <<>>
                        /\ UNCHANGED <<msgsAfterAppend, messages>>
                /\ IF r /= m.From THEN
                    /\ pc' = "StepLeader_2"
                    /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                    /\ UNCHANGED <<stack, leadTransferee, maxUncommittedSize, raftLog, term, electionElapsed, state, uncommittedSize>>
                    ELSE
                    UNCHANGED <<>>
                /\ IF /\ m.From = leadTransferee[r] /\ m.Index = raftLog_lastIndex[r] THEN
                    /\ pc' = "StepLeader_3"
                    /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                    /\ UNCHANGED <<stack, leadTransferee, maxUncommittedSize, raftLog, term, electionElapsed, state, uncommittedSize>>
                    ELSE
                    /\ UNCHANGED <<>>
                /\ IF m.From = leadTransferee[r] THEN
                    /\ pc' = "StepLeader_4"
                    /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                    /\ UNCHANGED <<stack, leadTransferee, maxUncommittedSize, raftLog, term, electionElapsed, state, uncommittedSize>>
                    ELSE
                    /\ UNCHANGED <<>>
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
                    /\ UNCHANGED <<leadTransferee, maxUncommittedSize, raftLog, term, electionElapsed, state, uncommittedSize>>
        [] m.Type = MsgHeartbeatResp ->
            /\ SendAppend(r, m.From)
            /\ pc' = stack[Len(stack)].backsite
            /\ stack' = Tail(stack)
            /\ info' = stack[Len(stack)].info
            /\ UNCHANGED <<leadTransferee, maxUncommittedSize, raftLog, term, electionElapsed, state, pendingConfIndex, uncommittedSize>>
        [] m.Type = MsgTransferLeader ->
            /\ IF /\ m.From # r THEN
                /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
                /\ leadTransferee' = [leadTransferee EXCEPT ![r] = m.From]
                /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
                /\ pc' = stack[Len(stack)].backsite
                /\ stack' = Tail(stack)
                /\ info' = stack[Len(stack)].info
                /\ UNCHANGED <<maxUncommittedSize, raftLog, term, state, pendingConfIndex, uncommittedSize>>
                ELSE
                /\ UNCHANGED <<>>
                /\ pc' = stack[Len(stack)].backsite
                /\ stack' = Tail(stack)
                /\ info' = stack[Len(stack)].info
                /\ UNCHANGED <<leadTransferee, maxUncommittedSize, msgsAfterAppend, raftLog, messages, term, electionElapsed, state, pendingConfIndex, uncommittedSize>>
        [] OTHER ->
            UNCHANGED <<state, term>>
            /\ pc' = stack[Len(stack)].backsite
            /\ stack' = Tail(stack)
            /\ info' = stack[Len(stack)].info
            /\ UNCHANGED <<leadTransferee, maxUncommittedSize, msgsAfterAppend, raftLog, messages, electionElapsed, pendingConfIndex, uncommittedSize>>
StepFollower(r, m) ==
    \//\ m.Type = MsgProp
        /\ /\ lead[r] /= None
            /\ Send(r, m)
            /\ UNCHANGED <<electionElapsed, term, state, lead>>
    \//\ m.Type \in {MsgApp, MsgHeartbeat, MsgSnap}
        /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
        /\ lead' = [lead EXCEPT ![r] = m.From]
        /\ HandleAppendEntries(r, m)
        /\ UNCHANGED <<msgsAfterAppend, term, state>>
    \//\ m.Type = MsgTransferLeader
        /\ /\ lead[r] /= None
            /\ m.To = lead[r]
            /\ Send(r, m)
            /\ UNCHANGED <<electionElapsed, term, state, lead>>
    \//\ m.Type = MsgForgetLeader
        /\ lead[r] /= None
        /\ lead' = [lead EXCEPT ![r] = None]
        /\ UNCHANGED <<msgsAfterAppend, messages, electionElapsed, term, state>>
    \//\ m.Type = MsgTimeoutNow
        /\ Hup(r, "campaignTransfer")
        /\ UNCHANGED <<msgsAfterAppend, messages, electionElapsed, lead>>
    \//\ m.Type = MsgReadIndex
        /\ lead[r] /= None
        /\ m.To = lead[r]
        /\ Send(r, m)
        /\ UNCHANGED <<electionElapsed, term, state, lead>>
StepCandidate(r, m) ==
    LET myVoteRespType == IF state[r] = "PreCandidate" THEN "MsgPreVoteResp" ELSE "MsgVoteResp" IN
        /\ CASE m.type = "MsgProp" ->
                UNCHANGED <<state, term>>
                /\ UNCHANGED <<raftLog_committed, Vote, msgsAfterAppend, trk_Votes, messages, raftLog_lastIndex, step, lead>>
            [] m.type = "MsgApp" ->
                /\ state' = [state EXCEPT ![r] = "Follower"]
                /\ lead' = [lead EXCEPT ![r] = m.from]
                /\ HandleAppendEntries(r, m)
                /\ UNCHANGED <<raftLog_committed, Vote, msgsAfterAppend, trk_Votes, term, raftLog_lastIndex, step>>
            [] m.type = "MsgHeartbeat" ->
                /\ state' = [state EXCEPT ![r] = "Follower"]
                /\ lead' = [lead EXCEPT ![r] = m.from]
                /\ HandleHeartbeat(r, m)
                /\ UNCHANGED <<Vote, msgsAfterAppend, trk_Votes, term, raftLog_lastIndex, step>>
            [] m.type = "MsgSnap" ->
                /\ state' = [state EXCEPT ![r] = "Follower"]
                /\ lead' = [lead EXCEPT ![r] = m.from]
                /\ HandleSnapshot(r, m)
                /\ UNCHANGED <<Vote, msgsAfterAppend, trk_Votes, step>>
            [] m.type = myVoteRespType ->
                /\ trk_Votes' = [trk_Votes EXCEPT ![r][id] = ~m.reject]
                /\ pc' = "StepCandidate_1"
                /\ info' = [args |-> <<r, m>>, temp |-> [myVoteRespType |-> myVoteRespType]]
                /\ UNCHANGED <<raftLog_committed, Vote, stack, raftLog_lastIndex, lead, msgsAfterAppend, messages, term, step, state>>
            [] m.type = "MsgTimeoutNow" ->
                UNCHANGED <<state, term>>
                /\ UNCHANGED <<raftLog_committed, Vote, msgsAfterAppend, trk_Votes, messages, raftLog_lastIndex, step, lead>>
            [] OTHER ->
                UNCHANGED <<state, term>>
                /\ UNCHANGED <<raftLog_committed, Vote, msgsAfterAppend, trk_Votes, messages, raftLog_lastIndex, step, lead>>
        /\ UNCHANGED MaxInflightMsgs
        /\ pc' = stack[Len(stack)].backsite
        /\ stack' = Tail(stack)
        /\ info' = stack[Len(stack)].info
RaftLog_isUpToDate(r, candLastID) ==
    /\ candLastID.Index > Len(raftLog[r])
    /\ candLastID.Term >= raftLog[r][Len(raftLog[r])].Term
ReduceUncommittedSize(r, s) ==
    IF s > uncommittedSize[r] THEN
        uncommittedSize' = [uncommittedSize EXCEPT ![r] = 0]
        ELSE
        uncommittedSize' = [uncommittedSize EXCEPT ![r] = uncommittedSize[r] - s]
Step(r, m) ==
    /\ IF m.Term = 0 THEN
        /\ UNCHANGED <<state, term, lead, step>>
        /\ UNCHANGED <<msgsAfterAppend, appliedTo, messages>>
        ELSE
        \//\ m.Term > term[r]
            /\ IF m.Type \in {MsgApp, MsgHeartbeat, MsgSnap} THEN
                /\ BecomeFollower(r, m.Term, m.From)
                /\ UNCHANGED <<msgsAfterAppend, appliedTo, messages>>
                ELSE
                /\ IF ~(m.Type \in {MsgVote, MsgPreVote}) THEN
                    /\ BecomeFollower(r, m.Term, m.From)
                    /\ UNCHANGED <<msgsAfterAppend, appliedTo, messages>>
                    ELSE
                    UNCHANGED <<state, term, lead, step>>
                    /\ UNCHANGED <<msgsAfterAppend, appliedTo, messages>>
        \//\ m.Term < term[r]
            /\ IF m.type \in {MsgApp, MsgHeartbeat} THEN
                /\ Send(r, [Type |-> MsgAppResp, To |-> m.from])
                /\ UNCHANGED <<appliedTo, term, step, state, lead>>
                ELSE
                IF m.type = MsgPreVote THEN
                    Send(r, [Type |-> MsgPreVoteResp, To |-> m.from, reject |-> TRUE])
                    /\ UNCHANGED <<appliedTo, term, step, state, lead>>
                    ELSE
                    IF m.type = MsgStorageAppendResp THEN
                        IF m.Snapshot /= None THEN
                            /\ pc' = "AppliedTo"
                            /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                            /\ UNCHANGED <<stableIndex, stack, Vote, lead, stableTerm, msgsAfterAppend, appliedTo, messages, term, step, electionElapsed, state>>
                            /\ stack' = [backsite |-> "Step_8", args |-> << m.Snapshot.Metadata.Index, r>>, info |-> info']
                            /\ UNCHANGED <<stableIndex, Vote, lead, stableTerm, msgsAfterAppend, appliedTo, messages, term, step, electionElapsed, state>>
                            ELSE
                            /\ UNCHANGED <<>>
                            /\ UNCHANGED <<msgsAfterAppend, appliedTo, messages, term, step, state, lead>>
                        ELSE
                        UNCHANGED <<>>
                        /\ UNCHANGED <<msgsAfterAppend, appliedTo, messages, term, step, state, lead>>
    /\ CASE m.type = MsgHup ->
            /\ pc' = "Step_1"
            /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
            /\ UNCHANGED <<stableIndex, stack, Vote, stableTerm, electionElapsed>>
        [] m.type = MsgStorageAppend ->
            /\ IF m.Index /= 0 THEN
                /\ stableIndex' = [stableIndex EXCEPT ![r] = m.Index]
                /\ stableTerm' = [stableTerm EXCEPT ![r] = m.Term]
                /\ pc' = stack[Len(stack)].backsite
                /\ stack' = Tail(stack)
                /\ info' = stack[Len(stack)].info
                /\ UNCHANGED <<Vote, electionElapsed>>
                ELSE
                /\ IF m.Snapshot /= None THEN
                    /\ stableIndex' = [stableIndex EXCEPT ![r] = m.Snapshot.Index]
                    /\ stableTerm' = [stableTerm EXCEPT ![r] = m.Snapshot.Term]
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
                    /\ UNCHANGED <<Vote, electionElapsed>>
                    ELSE
                    /\ UNCHANGED <<stableIndex, stableTerm>>
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
                    /\ UNCHANGED <<Vote, electionElapsed>>
        [] m.type = MsgStorageApplyResp ->
            /\ IF m.entries /= <<>> THEN
                /\ pc' = "AppliedTo"
                /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                /\ UNCHANGED <<stableIndex, stack, Vote, stableTerm, electionElapsed>>
                /\ stack' = [backsite |-> "Step_2", args |-> << Len(m.entries), r>>, info |-> info']
                /\ UNCHANGED <<stableIndex, Vote, stableTerm, electionElapsed>>
                ELSE
                /\ UNCHANGED <<>>
                /\ pc' = stack[Len(stack)].backsite
                /\ stack' = Tail(stack)
                /\ info' = stack[Len(stack)].info
                /\ UNCHANGED <<stableIndex, Vote, stableTerm, electionElapsed>>
        [] m.type \in {MsgVote, MsgPreVote} ->
            /\ LET canVote == IF Vote[r] = m.From THEN TRUE
                                ELSE /\ IF Vote[r] = None /\ lead[r] = None THEN TRUE
                                    ELSE /\ IF m.Type = "MsgPreVote" /\ m.Term > term[r] THEN TRUE
                                        ELSE FALSE  
                lastID == [Term |-> raftLog[r][Len(raftLog[r])].Term, Index |-> raftLog[r][Len(raftLog[r])].Index]
                candLastID == [Term |-> m.LogTerm, Index |-> m.Index] IN
                \//\ canVote
                    /\ RaftLog_isUpToDate(r, candLastID)
                    /\ IF m.Type = "MsgVote" THEN
                        /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
                        /\ Vote' = [Vote EXCEPT ![r] = m.From]
                        ELSE
                        /\ UNCHANGED <<electionElapsed, Vote>>
                    /\ pc' = "Step_3"
                    /\ info' = [args |-> <<r, m>>, temp |-> [canVote |-> canVote]]
                    /\ UNCHANGED <<stableIndex, stack, stableTerm>>
                \//\ ~canVote \/ ~RaftLog_isUpToDate(r, candLastID)
                    /\ pc' = "Step_4"
                    /\ info' = [args |-> <<r, m>>, temp |-> [canVote |-> canVote]]
                    /\ UNCHANGED <<stableIndex, stack, Vote, stableTerm, electionElapsed>>
        [] OTHER ->
            /\ CASE state'[r] = "Candidate" ->
                    /\ pc' = "StepCandidate"
                    /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                    /\ UNCHANGED <<stableIndex, stack, Vote, stableTerm, electionElapsed>>
                    /\ stack' = [backsite |-> "Step_5", args |-> << r, m>>, info |-> info']
                    /\ UNCHANGED <<stableIndex, Vote, stableTerm, electionElapsed>>
                [] state'[r] = "Follower" ->
                    /\ pc' = "Step_6"
                    /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                    /\ UNCHANGED <<stableIndex, stack, Vote, stableTerm, electionElapsed>>
                [] state'[r] = "Leader" ->
                    /\ pc' = "StepLeader"
                    /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                    /\ UNCHANGED <<stableIndex, stack, Vote, stableTerm, electionElapsed>>
                    /\ stack' = [backsite |-> "Step_7", args |-> << r, m>>, info |-> info']
                    /\ UNCHANGED <<stableIndex, Vote, stableTerm, electionElapsed>>
IsEmptySnap(s) ==
    /\ s.Metadata.Index = 0
    /\ s.Metadata.Term = 0
StepLeader_2_3_4(r, m) ==
                    /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
TickHeartbeat_2_3(r) ==
    /\ UNCHANGED <<vars>> 
    /\ pc' = stack[Len(stack)].backsite
    /\ stack' = Tail(stack)
    /\ info' = stack[Len(stack)].info
TickHeartbeat_1_2(r) ==
    /\ UNCHANGED <<vars>> 
    /\ pc' = stack[Len(stack)].backsite
    /\ stack' = Tail(stack)
    /\ info' = stack[Len(stack)].info
StepLeader_3_4(r, m) ==
                    /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
StepLeader_2_4(r, m) ==
                    /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
StepLeader_2_3(r, m) ==
                    /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
                /\ IF m.From = leadTransferee[r] THEN
                    /\ pc' = "StepLeader_2_3_4"
                    /\ info' = info
                    /\ UNCHANGED <<stack>>
                    ELSE
                    /\ UNCHANGED <<>>
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
StepCandidate_1_2(r, m) ==
        /\ UNCHANGED MaxInflightMsgs
        /\ pc' = stack[Len(stack)].backsite
        /\ stack' = Tail(stack)
        /\ info' = stack[Len(stack)].info
TickHeartbeat_2(r) ==
        /\ UNCHANGED electionElapsed
        /\ UNCHANGED leadTransferee
    /\ IF state[r] = StateLeader THEN
        /\ IF heartbeatElapsed[r] >= HeartbeatTimeout THEN
            /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![r] = 0]
            /\ pc' = "Step"
            /\ info' = [args |-> <<r>>, temp |-> <<>>]
            /\ UNCHANGED <<stack>>
            /\ stack' = [backsite |-> "TickHeartbeat_2_3", args |-> << r, [From |-> id[r], Type |-> MsgBeat]>>, info |-> info']
            ELSE
            /\ UNCHANGED heartbeatElapsed
            /\ pc' = stack[Len(stack)].backsite
            /\ stack' = Tail(stack)
            /\ info' = stack[Len(stack)].info
        ELSE
        /\ UNCHANGED heartbeatElapsed
        /\ pc' = stack[Len(stack)].backsite
        /\ stack' = Tail(stack)
        /\ info' = stack[Len(stack)].info
TickHeartbeat_1(r) ==
        /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
        /\ IF state[r] = StateLeader /\ leadTransferee[r] /= None THEN
            /\ leadTransferee' = [leadTransferee EXCEPT ![r] = None]
            ELSE
            /\ UNCHANGED leadTransferee
    /\ IF state[r] = StateLeader THEN
        /\ IF heartbeatElapsed[r] >= HeartbeatTimeout THEN
            /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![r] = 0]
            /\ pc' = "Step"
            /\ info' = [args |-> <<r>>, temp |-> <<>>]
            /\ UNCHANGED <<stack>>
            /\ stack' = [backsite |-> "TickHeartbeat_1_2", args |-> << r, [From |-> id[r], Type |-> MsgBeat]>>, info |-> info']
            ELSE
            /\ UNCHANGED heartbeatElapsed
            /\ pc' = stack[Len(stack)].backsite
            /\ stack' = Tail(stack)
            /\ info' = stack[Len(stack)].info
        ELSE
        /\ UNCHANGED heartbeatElapsed
        /\ pc' = stack[Len(stack)].backsite
        /\ stack' = Tail(stack)
        /\ info' = stack[Len(stack)].info
TickElection_1(r) ==
    /\ UNCHANGED <<vars>> 
    /\ pc' = stack[Len(stack)].backsite
    /\ stack' = Tail(stack)
    /\ info' = stack[Len(stack)].info
Step_8(r, m) ==
    /\ CASE m.type = MsgHup ->
            /\ pc' = "Step_1"
            /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
            /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
        [] m.type = MsgStorageAppend ->
            /\ IF m.Index /= 0 THEN
                /\ stableIndex' = [stableIndex EXCEPT ![r] = m.Index]
                /\ stableTerm' = [stableTerm EXCEPT ![r] = m.Term]
                /\ pc' = stack[Len(stack)].backsite
                /\ stack' = Tail(stack)
                /\ info' = stack[Len(stack)].info
                /\ UNCHANGED <<Vote, electionElapsed>>
                ELSE
                /\ IF m.Snapshot /= None THEN
                    /\ stableIndex' = [stableIndex EXCEPT ![r] = m.Snapshot.Index]
                    /\ stableTerm' = [stableTerm EXCEPT ![r] = m.Snapshot.Term]
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
                    /\ UNCHANGED <<Vote, electionElapsed>>
                    ELSE
                    /\ UNCHANGED <<stableIndex, stableTerm>>
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
                    /\ UNCHANGED <<Vote, electionElapsed>>
        [] m.type = MsgStorageApplyResp ->
            /\ IF m.entries /= <<>> THEN
                /\ pc' = "AppliedTo"
                /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
                /\ stack' = [backsite |-> "Step_2", args |-> << Len(m.entries), r>>, info |-> info']
                /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
                ELSE
                /\ UNCHANGED <<>>
                /\ pc' = stack[Len(stack)].backsite
                /\ stack' = Tail(stack)
                /\ info' = stack[Len(stack)].info
                /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
        [] m.type \in {MsgVote, MsgPreVote} ->
            /\ LET canVote == IF Vote[r] = m.From THEN TRUE
                                ELSE /\ IF Vote[r] = None /\ lead[r] = None THEN TRUE
                                    ELSE /\ IF m.Type = "MsgPreVote" /\ m.Term > term[r] THEN TRUE
                                        ELSE FALSE  
                lastID == [Term |-> raftLog[r][Len(raftLog[r])].Term, Index |-> raftLog[r][Len(raftLog[r])].Index]
                candLastID == [Term |-> m.LogTerm, Index |-> m.Index] IN
                \//\ canVote
                    /\ RaftLog_isUpToDate(r, candLastID)
                    /\ IF m.Type = "MsgVote" THEN
                        /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
                        /\ Vote' = [Vote EXCEPT ![r] = m.From]
                        ELSE
                        /\ UNCHANGED <<electionElapsed, Vote>>
                    /\ pc' = "Step_3"
                    /\ info' = [args |-> <<r, m>>, temp |-> [canVote |-> canVote]]
                    /\ UNCHANGED <<stableTerm, stableIndex>>
                \//\ ~canVote \/ ~RaftLog_isUpToDate(r, candLastID)
                    /\ pc' = "Step_4"
                    /\ info' = [args |-> <<r, m>>, temp |-> [canVote |-> canVote]]
                    /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
        [] OTHER ->
            /\ CASE state[r] = "Candidate" ->
                    /\ pc' = "StepCandidate"
                    /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                    /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
                    /\ stack' = [backsite |-> "Step_5", args |-> << r, m>>, info |-> info']
                    /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
                [] state[r] = "Follower" ->
                    /\ pc' = "Step_6"
                    /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                    /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
                [] state[r] = "Leader" ->
                    /\ pc' = "StepLeader"
                    /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                    /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
                    /\ stack' = [backsite |-> "Step_7", args |-> << r, m>>, info |-> info']
                    /\ UNCHANGED <<stableTerm, stableIndex, Vote, electionElapsed>>
Step_7(r, m) ==
    /\ UNCHANGED <<vars>> 
    /\ pc' = stack[Len(stack)].backsite
    /\ stack' = Tail(stack)
    /\ info' = stack[Len(stack)].info
Step_6(r, m) ==
                    /\ StepFollower(r, m)
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
Step_5(r, m) ==
    /\ UNCHANGED <<vars>> 
    /\ pc' = stack[Len(stack)].backsite
    /\ stack' = Tail(stack)
    /\ info' = stack[Len(stack)].info
Step_4(r, m) ==
                    /\ Send(r, [Type |-> IF m.Type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp", To |-> m.From, Term |-> term[r], reject |-> TRUE])
                    /\ UNCHANGED <<electionElapsed, Vote>>
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
Step_3(r, m) ==
                    /\ Send(r, [Type |-> IF m.Type = "MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp", To |-> m.From, Term |-> m.Term, reject |-> FALSE])
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
Step_2(r, m) ==
                /\ ReduceUncommittedSize(r, Len(m.entries))
                /\ pc' = stack[Len(stack)].backsite
                /\ stack' = Tail(stack)
                /\ info' = stack[Len(stack)].info
Step_1(r, m) ==
            /\ Hup(r, "CampaignPreElection")
            /\ pc' = stack[Len(stack)].backsite
            /\ stack' = Tail(stack)
            /\ info' = stack[Len(stack)].info
StepLeader_4(r, m) ==
                    /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
StepLeader_3(r, m) ==
                    /\ Send(r, [Type |-> MsgTimeoutNow, To |-> m.From])
                /\ IF m.From = leadTransferee[r] THEN
                    /\ pc' = "StepLeader_3_4"
                    /\ info' = info
                    /\ UNCHANGED <<stack>>
                    ELSE
                    /\ UNCHANGED <<>>
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
StepLeader_2(r, m) ==
                    /\ MaybeSendAppend(r, m.From, FALSE)
                /\ IF /\ m.From = leadTransferee[r] /\ m.Index = raftLog_lastIndex[r] THEN
                    /\ pc' = "StepLeader_2_3"
                    /\ info' = info
                    /\ UNCHANGED <<stack>>
                    ELSE
                    /\ UNCHANGED <<>>
                /\ IF m.From = leadTransferee[r] THEN
                    /\ pc' = "StepLeader_2_4"
                    /\ info' = info
                    /\ UNCHANGED <<stack>>
                    ELSE
                    /\ UNCHANGED <<>>
                    /\ pc' = stack[Len(stack)].backsite
                    /\ stack' = Tail(stack)
                    /\ info' = stack[Len(stack)].info
StepLeader_1(r, m) ==
            /\ BcastAppend(r)
            /\ pc' = stack[Len(stack)].backsite
            /\ stack' = Tail(stack)
            /\ info' = stack[Len(stack)].info
AppliedTo_1(index, r) ==
    /\ IF appliedTo'[r] >= pendingConfIndex[r] /\ state[r] = "StateLeader" THEN
        /\ messages' = Append(messages, [Type |-> "ConfChangeV2", Term |-> term[r], From |-> r])
        /\ pc' = stack[Len(stack)].backsite
        /\ stack' = Tail(stack)
        /\ info' = stack[Len(stack)].info
        ELSE
        /\ messages' = messages
        /\ pc' = stack[Len(stack)].backsite
        /\ stack' = Tail(stack)
        /\ info' = stack[Len(stack)].info
StepCandidate_1(r, m) ==
                /\ LET PollResult == Poll(r, m.from, m.type, ~m.reject) IN
                    /\ CASE PollResult.result = "VoteWon" ->
                            IF state[r] = "PreCandidate" THEN
                                /\ pc' = "Campaign"
                                /\ info' = [args |-> <<r, m>>, temp |-> <<>>]
                                /\ UNCHANGED <<stack, Vote, msgsAfterAppend, messages, term, step, state, lead>>
                                /\ stack' = [backsite |-> "StepCandidate_1_2", args |-> << r, "campaignPreElection">>, info |-> info']
                                /\ UNCHANGED <<Vote, msgsAfterAppend, messages, term, step, state, lead>>
                                ELSE
                                /\ state' = [state EXCEPT ![r] = "Leader"]
                                /\ BcastAppend(r)
                                /\ UNCHANGED <<Vote, msgsAfterAppend, term, step, lead>>
                        [] PollResult.result = "VoteLost" ->
                            /\ state' = [state EXCEPT ![r] = "Follower"]
                            /\ lead' = [lead EXCEPT ![r] = "None"]
                            /\ term' = [term EXCEPT ![r] = term[r]]
                            /\ UNCHANGED <<Vote, msgsAfterAppend, messages, step>>
                        [] OTHER ->
                            UNCHANGED <<state, term>>
                            /\ UNCHANGED <<Vote, msgsAfterAppend, messages, step, lead>>
        /\ UNCHANGED MaxInflightMsgs
        /\ pc' = stack[Len(stack)].backsite
        /\ stack' = Tail(stack)
        /\ info' = stack[Len(stack)].info
        /\ UNCHANGED <<stack, pc, info>>
Campaign_2(r, t) ==
            /\ term' = [r |-> term[r]]
        /\ LET ids == DOMAIN trk_Votes[r] IN
            /\ \A idd \in ids:
                IF idd = r.id THEN
                    /\ msgsAfterAppend' = Append(msgsAfterAppend, [To |-> idd, Term |-> term'[r], Type |-> info.temp.voteMsg])
                    ELSE /\ Send(r, [To |-> id, Term |-> term'[r], Type |-> info.temp.voteMsg'[r], Index |-> raftLog[r][Len(raftLog[r])].Index, LogTerm |-> raftLog[r][Len(raftLog[r])].Term])
        
        /\ UNCHANGED <<MaxInflightMsgs>>
        /\ pc' = stack[Len(stack)].backsite
        /\ stack' = Tail(stack)
        /\ info' = stack[Len(stack)].info
Campaign_1(r, t) ==
            /\ term' = [r |-> term[r] + 1]
        /\ LET ids == DOMAIN trk_Votes[r] IN
            /\ \A idd \in ids:
                IF idd = r.id THEN
                    /\ msgsAfterAppend' = Append(msgsAfterAppend, [To |-> idd, Term |-> term'[r], Type |-> info.temp.voteMsg])
                    ELSE /\ Send(r, [To |-> id, Term |-> term'[r], Type |-> info.temp.voteMsg'[r], Index |-> raftLog[r][Len(raftLog[r])].Index, LogTerm |-> raftLog[r][Len(raftLog[r])].Term])
        
        /\ UNCHANGED <<MaxInflightMsgs>>
        /\ pc' = stack[Len(stack)].backsite
        /\ stack' = Tail(stack)
        /\ info' = stack[Len(stack)].info
LoadState(r, state_Commit, state_Term, state_Vote) ==
    /\ state_Commit >= raftLog_committed[r]
    /\ state_Commit <= raftLog_lastIndex[r]
    /\ raftLog_committed' = [raftLog_committed EXCEPT ![r] = state_Commit]
    /\ term' = [term EXCEPT ![r] = state_Term]
    /\ Vote' = [Vote EXCEPT ![r] = state_Vote]
AppliedSnap(r, snap) ==
    /\ snap.Index > snapshot[r].Index
    /\ snapshot[r] = snap
AbortLeaderTransfer(r) ==
    /\ leadTransferee' = [leadTransferee EXCEPT ![r] = None]
TickHeartbeat(r) ==
    /\ heartbeatElapsed' = [heartbeatElapsed EXCEPT ![r] = @ + 1]
    /\ electionElapsed' = [electionElapsed EXCEPT ![r] = @ + 1]
    /\ IF electionElapsed'[r] >= electionTimeout[r] THEN
        /\ pc' = "TickHeartbeat_1"
        /\ info' = [args |-> <<r>>, temp |-> <<>>]
        ELSE
        /\ pc' = "TickHeartbeat_2"
        /\ info' = [args |-> <<r>>, temp |-> <<>>]
checkQuorum ==
    /\ Cardinality(active_nodes) >= Cardinality(Nodes) \div 2 + 1
BecomeLeader(r) ==
    /\ state[r] /= StateFollower
    /\ step' = [step EXCEPT ![r] = stepLeader]
    /\ Vote' = [Vote EXCEPT ![r] = None]
    /\ lead' = [lead EXCEPT ![r] = id[r]]
    /\ state' = [state EXCEPT ![r] = StateLeader]
    /\ pendingConfIndex' = [pendingConfIndex EXCEPT ![r] = raftLog_lastIndex[r]]
    /\ raftLog_lastIndex' = [raftLog_lastIndex EXCEPT ![r] = raftLog_lastIndex[r] + 1]
    /\ raftLog' = [raftLog EXCEPT ![r] = Append(raftLog[r], [Term |-> term[r], Data |-> None])]
MaybeSendSnapshot(r, to, pr) ==
    /\ LET sindex == snapshot[r].Index
        sterm == snapshot[r].Term IN
        /\ ~IsEmptySnap(snapshot[r])
        /\ Send(r, [Type |-> "MsgSnap", To |-> to, Snapshot |-> snapshot[r]])
TickElection(r) ==
    /\ IF Promotable(r) /\ electionElapsed[r] >= electionTimeout[r] THEN
        /\ electionElapsed' = [electionElapsed EXCEPT ![r] = 0]
        /\ pc' = "Step"
        /\ info' = [args |-> <<r>>, temp |-> <<>>]
        /\ UNCHANGED <<stack>>
        /\ stack' = [backsite |-> "TickElection_1", args |-> << r, [Type |-> "MsgHup", From |-> id[r]]>>, info |-> info']
        ELSE
        /\ electionElapsed' = [electionElapsed EXCEPT ![r] = @ + 1]
        /\ UNCHANGED <<stack, pc, info>>
other_vars ==
    <<uncommittedSize, maxUncommittedSize, trk_Progress, active_nodes, heartbeatElapsed, leadTransferee>>
snapshot_vars ==
    <<snapshot>>
stable_vars ==
    <<stableIndex, stableTerm>>
election_vars ==
    <<electionElapsed, electionTimeout, campaignType, trk_Votes, pendingConfIndex>>
log_vars ==
    <<raftLog, raftLog_committed, raftLog_lastIndex, appliedTo, messages, msgsAfterAppend>>
node_vars ==
    <<id, state, term, Vote, lead, step>>
HandleStepLeader_2_3_4 ==
    /\ pc = "StepLeader_2_3_4"
    /\ StepLeader_2_3_4(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleTickHeartbeat_2_3 ==
    /\ pc = "TickHeartbeat_2_3"
    /\ TickHeartbeat_2_3(info.args[1])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleTickHeartbeat_1_2 ==
    /\ pc = "TickHeartbeat_1_2"
    /\ TickHeartbeat_1_2(info.args[1])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepLeader_3_4 ==
    /\ pc = "StepLeader_3_4"
    /\ StepLeader_3_4(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepLeader_2_4 ==
    /\ pc = "StepLeader_2_4"
    /\ StepLeader_2_4(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepLeader_2_3 ==
    /\ pc = "StepLeader_2_3"
    /\ StepLeader_2_3(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepCandidate_1_2 ==
    /\ pc = "StepCandidate_1_2"
    /\ StepCandidate_1_2(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleTickHeartbeat_2 ==
    /\ pc = "TickHeartbeat_2"
    /\ TickHeartbeat_2(info.args[1])
    /\ UNCHANGED <<stableIndex, trk_Progress, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, appliedTo, messages, step, pendingConfIndex, snapshot, uncommittedSize>>
HandleTickHeartbeat_1 ==
    /\ pc = "TickHeartbeat_1"
    /\ TickHeartbeat_1(info.args[1])
    /\ UNCHANGED <<stableIndex, trk_Progress, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, appliedTo, messages, step, pendingConfIndex, snapshot, uncommittedSize>>
HandleTickElection_1 ==
    /\ pc = "TickElection_1"
    /\ TickElection_1(info.args[1])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStep_8 ==
    /\ pc = "Step_8"
    /\ Step_8(info.args[1], info.args[2])
    /\ UNCHANGED <<trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, pendingConfIndex, snapshot, uncommittedSize>>
HandleStep_7 ==
    /\ pc = "Step_7"
    /\ Step_7(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStep_6 ==
    /\ pc = "Step_6"
    /\ Step_6(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, id, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, stableTerm, heartbeatElapsed, appliedTo, step, pendingConfIndex, snapshot, uncommittedSize>>
HandleStep_5 ==
    /\ pc = "Step_5"
    /\ Step_5(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStep_4 ==
    /\ pc = "Step_4"
    /\ Step_4(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, pendingConfIndex, snapshot, uncommittedSize>>
HandleStep_3 ==
    /\ pc = "Step_3"
    /\ Step_3(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStep_2 ==
    /\ pc = "Step_2"
    /\ Step_2(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot>>
HandleStep_1 ==
    /\ pc = "Step_1"
    /\ Step_1(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, id, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepLeader_4 ==
    /\ pc = "StepLeader_4"
    /\ StepLeader_4(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepLeader_3 ==
    /\ pc = "StepLeader_3"
    /\ StepLeader_3(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepLeader_2 ==
    /\ pc = "StepLeader_2"
    /\ StepLeader_2(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepLeader_1 ==
    /\ pc = "StepLeader_1"
    /\ StepLeader_1(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleAppliedTo_1 ==
    /\ pc = "AppliedTo_1"
    /\ AppliedTo_1(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepCandidate_1 ==
    /\ pc = "StepCandidate_1"
    /\ StepCandidate_1(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, id, active_nodes, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, stableTerm, heartbeatElapsed, appliedTo, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleCampaign_2 ==
    /\ pc = "Campaign_2"
    /\ Campaign_2(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleCampaign_1 ==
    /\ pc = "Campaign_1"
    /\ Campaign_1(info.args[1], info.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleLoadState(r, state_Commit, state_Term, state_Vote) ==
    /\ pc = Nil
    /\ LoadState(r, state_Commit, state_Term, state_Vote)
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, id, state, active_nodes, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleAppliedSnap(r, snap) ==
    /\ pc = Nil
    /\ AppliedSnap(r, snap)
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleAbortLeaderTransfer(r) ==
    /\ pc = Nil
    /\ AbortLeaderTransfer(r)
    /\ UNCHANGED <<stableIndex, trk_Progress, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleTickHeartbeat(r) ==
    /\ pc = Nil
    /\ TickHeartbeat(r)
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, appliedTo, messages, step, pendingConfIndex, snapshot, uncommittedSize>>
HandlecheckQuorum ==
    /\ pc = Nil
    /\ checkQuorum
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleBecomeLeader(r) ==
    /\ pc = Nil
    /\ BecomeLeader(r)
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, trk_Votes, term, id, active_nodes, raftLog_committed, campaignType, maxUncommittedSize, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, electionElapsed, snapshot, uncommittedSize>>
HandleMaybeSendSnapshot(r, to, pr) ==
    /\ pc = Nil
    /\ MaybeSendSnapshot(r, to, pr)
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleTickElection(r) ==
    /\ pc = Nil
    /\ TickElection(r)
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, pendingConfIndex, snapshot, uncommittedSize>>
HandleStep ==
    /\ pc = "Step"
    /\ Step(stack.args[1], stack.args[2])
    /\ UNCHANGED <<trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, id, active_nodes, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, heartbeatElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepLeader ==
    /\ pc = "StepLeader"
    /\ StepLeader(stack.args[1], stack.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, electionTimeout, trk_Votes, id, active_nodes, Vote, raftLog_committed, campaignType, raftLog_lastIndex, lead, stableTerm, heartbeatElapsed, appliedTo, step, snapshot>>
HandleAppliedTo ==
    /\ pc = "AppliedTo"
    /\ AppliedTo(stack.args[1], stack.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleStepCandidate ==
    /\ pc = "StepCandidate"
    /\ StepCandidate(stack.args[1], stack.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, id, active_nodes, campaignType, maxUncommittedSize, stableTerm, heartbeatElapsed, appliedTo, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
HandleCampaign ==
    /\ pc = "Campaign"
    /\ Campaign(stack.args[1], stack.args[2])
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, id, active_nodes, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
Handleother_vars ==
    /\ pc = Nil
    /\ other_vars
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
Handlesnapshot_vars ==
    /\ pc = Nil
    /\ snapshot_vars
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
Handlestable_vars ==
    /\ pc = Nil
    /\ stable_vars
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
Handleelection_vars ==
    /\ pc = Nil
    /\ election_vars
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
Handlelog_vars ==
    /\ pc = Nil
    /\ log_vars
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
Handlenode_vars ==
    /\ pc = Nil
    /\ node_vars
    /\ UNCHANGED <<stableIndex, trk_Progress, leadTransferee, electionTimeout, raftLog, trk_Votes, term, id, state, active_nodes, Vote, raftLog_committed, campaignType, maxUncommittedSize, raftLog_lastIndex, lead, stableTerm, msgsAfterAppend, heartbeatElapsed, appliedTo, messages, step, electionElapsed, pendingConfIndex, snapshot, uncommittedSize>>
