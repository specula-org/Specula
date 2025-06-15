--------------------------------- MODULE etcd_leader_election ---------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Servers, None, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp, MsgBeat, MsgCheckQuorum, stepFollower, stepCandidate, stepLeader, Parameters

CONSTANTS StateFollower, StateCandidate, StateLeader

VARIABLES state, Term, Vote, lead, step, msgs, accepted, rejected

VARIABLES netman, netcmd, pc

INSTANCE FifoNetwork WITH FLUSH_DISCONN <- TRUE, NULL_MSG <- None, _msgs <- msgs, _netman <- netman, _netcmd <- netcmd

VARIABLES inv

SelectSeqWithIdx(s, Test(_,_)) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0 THEN 
            <<>>
            ELSE 
            IF Test(s[i], i) THEN
                Append(F[i-1], s[i])
                ELSE 
                F[i-1]
    IN
        F[Len(s)]
        
raft_becomeFollower(s, term, lead1) ==
    /\ step' = [step EXCEPT ![s] = stepFollower]
    /\ IF Term[s] # term THEN
        /\ Term' = [Term EXCEPT ![s] = term]
        /\ Vote' = [Vote EXCEPT ![s] = None]
        ELSE
        /\ UNCHANGED <<Term, Vote>>
    /\ lead' = [lead EXCEPT ![s] = lead1]
    /\ state' = [state EXCEPT ![s] = StateFollower]

raft_becomeCandidate(s) == 
    /\ step' = [step EXCEPT ![s] = stepCandidate]
    /\ Term' = [Term EXCEPT ![s] = Term[s] + 1]
    /\ Vote' = [Vote EXCEPT ![s] = s]
    /\ state' = [state EXCEPT ![s] = StateCandidate]

raft_becomeLeader(s) == 
    /\ step' = [step EXCEPT ![s] = stepLeader]
    /\ lead' = [lead EXCEPT ![s] = s]
    /\ state' = [state EXCEPT ![s] = StateLeader]

raft_campaign(i) == 
    /\ raft_becomeCandidate(i)
    /\ LET dsts == Servers \ {i} size == Cardinality(dsts) F[n \in 0..size] ==
            IF n = 0 THEN
                <<<<>>, dsts>>
                ELSE
                LET ms == F[n-1][1] s == CHOOSE j \in F[n-1][2]: TRUE m == [ src |-> i, dst |-> s, Type |-> MsgVote, Term |-> Term'[i]] remaining == F[n-1][2] \ {s}
                IN 
                    <<Append(ms, m), remaining>>
        IN 
            /\ NetUpdate2(NetmanIncField("n_elec", NetBatchAddMsg(F[size][1])), <<"ElectionTimeout", i>>)
    /\ UNCHANGED <<accepted, lead, rejected >>

stepCandidate_f(r, m) == 
    /\ IF m.Type = MsgHeartbeat THEN
        /\ raft_becomeFollower(r, m.Term, m.src)
        /\ UNCHANGED <<accepted, rejected>>
        ELSE
        /\ IF m.Type = MsgVoteResp THEN
            /\ IF ~m.Reject THEN
                /\ accepted' = [accepted EXCEPT ![r] = accepted[r] + 1]
                /\ UNCHANGED <<rejected>>
                ELSE
                /\ rejected' = [rejected EXCEPT ![r] = rejected[r] + 1]
                /\ UNCHANGED <<accepted>>
            /\ IF (2*accepted[r]) > Cardinality(Servers) THEN
                /\ raft_becomeLeader(r)
                /\ UNCHANGED <<Term, Vote>>
                ELSE
                /\ IF (2*rejected[r]) > Cardinality(Servers) THEN
                    /\ raft_becomeFollower(r, Term[r], None)
                    ELSE
                    /\ UNCHANGED <<Term, step, lead, state, Vote>>
            ELSE
            /\ UNCHANGED <<Term, step, lead, state, Vote, accepted, rejected>>

stepFollower_f(r, m) == 
    /\ IF m.Type = MsgVote THEN
        /\ LET canVote == Vote[r] = m.src \/ (Vote[r] = None /\ lead[r] = None) IN
            /\ IF canVote THEN
                /\ Vote' = [Vote EXCEPT ![r] = m.src]
                /\ NetUpdate2(NetmanIncField("n_send", NetReplyMsg([src|-> r, dst|-> m.src, Term|-> Term[r], Type|-> MsgVoteResp, Reject|-> FALSE], m)), <<"VoteResp", r>>)
                ELSE
                /\ NetUpdate2(NetmanIncField("n_send", NetReplyMsg([src|-> r, dst|-> m.src, Term|-> Term[r], Type|-> MsgVoteResp, Reject|-> TRUE], m)), <<"VoteResp", r>>)
                /\ UNCHANGED <<Vote>>
        ELSE
        /\ UNCHANGED <<Vote, netcmd, netman, msgs>>

raft_Step(s, m) == 
    /\ IF m.Term > Term[s] THEN
        /\ IF m.Type = MsgHeartbeat THEN
            /\ raft_becomeFollower(s, m.Term, m.src)
            ELSE
            /\ raft_becomeFollower(s, m.Term, None)
        ELSE
        /\ UNCHANGED <<Term, step, lead, state, Vote>>
    /\ IF m.Term < Term'[s] THEN
        /\ IF m.Type = MsgHeartbeat THEN
            /\ NetUpdate2(NetmanIncField("n_send", NetReplyMsg([src|-> s, dst|-> m.src, Term|-> Term'[s], Type|-> MsgHeartbeatResp], m)), <<"HeartbeatResp", s>>)
            /\ UNCHANGED <<Term, step, lead, state, Vote, accepted, rejected>>
            ELSE
            /\ UNCHANGED <<Term, step, lead, state, Vote, accepted, rejected, netcmd, netman, msgs>>
        /\ UNCHANGED <<pc>>
        ELSE
        /\ pc' = <<s, m>>
        /\ UNCHANGED <<accepted, rejected, netcmd, netman, msgs>>

raft_Step_1(s, m) == 
    /\ IF m.Type = MsgVote THEN
        /\ LET canVote == (Vote[s] = m.src \/ (Vote[s] = None /\ lead[s] = None)) IN
            /\ IF canVote THEN
                /\ Vote' = [Vote EXCEPT ![s] = m.src]
                /\ NetUpdate2(NetmanIncField("n_send", NetReplyMsg([src|-> s, dst|-> m.src, Term|-> Term[s], Type|-> MsgVoteResp, Reject|-> FALSE], m)), <<"VoteResp", s>>)
                ELSE
                /\ NetUpdate2(NetmanIncField("n_send", NetReplyMsg([src|-> s, dst|-> m.src, Term|-> Term[s], Type|-> MsgVoteResp, Reject|-> TRUE], m)), <<"VoteResp", s>>)
                /\ UNCHANGED <<Vote>>  
            /\ UNCHANGED <<Term, step, lead, state, accepted, rejected>>
        ELSE
        /\ IF state[s] = StateFollower THEN
            /\ stepFollower_f(s, m)
            /\ UNCHANGED <<Term, step, lead, state, accepted, rejected>>
            ELSE
            IF state[s] = StateCandidate THEN
                /\ stepCandidate_f(s, m)
                /\ UNCHANGED <<netcmd, netman, msgs>>
                ELSE
                /\ UNCHANGED <<Term, step, lead, state, Vote, accepted, rejected, netcmd, netman, msgs>>
    /\ pc' = None

====
