------------------------------- MODULE base -------------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, Bags, TLC

(***************************************************************************
Category A. etcd-raft incremental revision 3d0faba4ee302b1b61b3eaa084fafc284854ac07
(protocol files aligned with 46580dcf61734b12ae757dbabdf31c2b862acd68).
Source references are relative to ../../source. S1..S6 and the first U1..U5
are retained history; V02-U1..U5 are the current scenarios in modeling-brief.md.
Core functions below are pure record transformations: one Step/Tick is atomic.
Caller completion, transport, application, and Advance are separate actions.
Prefix witnesses are ghosts, never consulted by protocol decision guards.
See model-notes.md for caller variants, finite abstraction, and coverage gaps.
***************************************************************************)
CONSTANTS Server, BootPeers, Joining, RawNodes, PreVoteNodes, CheckQuorumNodes,
          NoForwardNodes, RequestId, PayloadWeights, EncodedWeights,
          ElectionTick, HeartbeatTick, MaxInflight, MaxMsgSize, MaxReadySize,
          MaxUncommitted, SendPolicy, PersistPolicy, EarlyAdvance,
          ReadFence, CancelChanges, CancelUnknownRemovals, RecoveryMode
ASSUME /\ Server # {} /\ 0 \notin Server
       /\ Joining \subseteq Server /\ RawNodes \subseteq Server
       /\ {BootPeers[k] : k \in DOMAIN BootPeers} = Server \ Joining
       /\ Len(BootPeers) = Cardinality(Server \ Joining)
       /\ PreVoteNodes \subseteq Server /\ CheckQuorumNodes \subseteq Server
       /\ NoForwardNodes \subseteq Server /\ CancelChanges \subseteq RequestId
       /\ 0 \notin RequestId
       /\ \A w\in PayloadWeights:w>=0
       /\ \A z\in EncodedWeights:z>0
       /\ ElectionTick > HeartbeatTick /\ HeartbeatTick > 0 /\ MaxInflight > 0
       /\ SendPolicy \in {"Strict", "SameBatch"}
       /\ PersistPolicy \in {"Atomic", "EntriesHSnap", "Parallel"}
       /\ RecoveryMode \in {"Replay", "AppliedAdapter"}
       /\ ReadFence \in {"Inclusive", "Strict"}

VARIABLES raft, disk, ready, application, requests, wire, history, quality
protocolVars == <<raft, disk, ready, application, requests, wire, history>>
vars == <<protocolVars,quality>>

Min(a,b) == IF a < b THEN a ELSE b
Max(a,b) == IF a > b THEN a ELSE b
MaxSet(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y
MinSet(S) == CHOOSE x \in S : \A y \in S : x <= y
Prefix(s,k) == SubSeq(s,1,Min(k,Len(s)))
Suffix(s,k) == SubSeq(s,k,Len(s))
SeqSet(s) == {s[k] : k \in DOMAIN s}
Compatible(a,b) == Prefix(a,Min(Len(a),Len(b))) = Prefix(b,Min(Len(a),Len(b)))
Covers(a,b) == Len(a) >= Len(b) /\ Prefix(a,Len(b)) = b
AddBag(b,x) == b (+) SetToBag({x})
RemoveBag(b,x) == b (-) SetToBag({x})
BagSeq(s) == [x \in SeqSet(s) |-> Cardinality({k \in DOMAIN s : s[k] = x})]
RECURSIVE SetSequence(_)
SetSequence(xs) == IF xs={} THEN <<>> ELSE
    LET x==CHOOSE y\in xs:TRUE IN <<x>> \o SetSequence(xs\{x})
DefaultBootPeers == SetSequence(Server\Joining)
EmptyHS == [term |-> 0, vote |-> 0, commit |-> 0]
\* tracker/tracker.go:25-77. voters is the incoming half and outgoing is the
\* retained old half while joint. learnersNext stages demotions until leave.
EmptyConfig == [voters |-> {}, outgoing |-> {}, learners |-> {},
                learnersNext |-> {}, autoLeave |-> FALSE]
BootConfig == [voters |-> Server \ Joining, outgoing |-> {}, learners |-> {},
               learnersNext |-> {}, autoLeave |-> FALSE]
EmptySnapshot == [index |-> 0, term |-> 0, hist |-> <<>>, config |-> EmptyConfig]
Change(k,target) == [kind |-> k, target |-> target]
Entry(t,i,k,id,target,w,z) ==
    [term |-> t, index |-> i, kind |-> k, id |-> id, target |-> target,
     changes |-> IF k\in {"AddVoter","AddLearner","Remove","Update"}
                THEN <<Change(k,target)>> ELSE <<>>,
     transition |-> "Legacy", weight |-> w, encoded |-> z]
V2Entry(t,i,id,changes,transition,w,z) ==
    [term |-> t, index |-> i, kind |-> "V2", id |-> id, target |-> 0,
     changes |-> changes, transition |-> transition, weight |-> w, encoded |-> z]
RequestEntry(q,id) == IF q.kind="V2"
    THEN V2Entry(0,0,id,q.changes,q.transition,q.weight,q.encoded)
    ELSE Entry(0,0,q.kind,id,q.target,q.weight,q.encoded)
\* Default abstract weights; Trace overrides these with measured protobuf sizes.
BootstrapPayload == 1
BootstrapEncoded == 1
EmptyEncoded == 1
\* Empty ConfChangeV2 marshals to a two-byte payload and a ten-byte Entry in
\* this source revision. Trace domains retain those concrete sizes; compact MC
\* domains map them to their largest abstract representatives.
AutoLeaveWeight == IF 2\in PayloadWeights /\ 10\in EncodedWeights
                   THEN 2 ELSE MaxSet(PayloadWeights)
AutoLeaveEncoded == IF 10\in EncodedWeights THEN 10 ELSE MaxSet(EncodedWeights)
BootLog == [k \in 1..Len(BootPeers) |-> Entry(1,k,"AddVoter",0,BootPeers[k],BootstrapPayload,BootstrapEncoded)]
LegacyConfKinds == {"AddVoter","AddLearner","Remove","Update"}
ConfKinds == LegacyConfKinds \cup {"V2"}
Kinds == LegacyConfKinds \cup {"Normal"}
RECURSIVE Weight(_), Encoded(_)
Weight(es) == IF es = <<>> THEN 0 ELSE Head(es).weight + Weight(Tail(es))
Encoded(es) == IF es = <<>> THEN 0 ELSE Head(es).encoded + Encoded(Tail(es))
\* util.go:129-142; retain oversized first entry and maximal fitting prefix.
LimitSize(es,cap) == IF es = <<>> THEN es ELSE
    Prefix(es, MaxSet({k \in 1..Len(es) : k = 1 \/ Encoded(Prefix(es,k)) <= cap}))

\* tracker/progress.go:79-209; S2/S4, no invariant Next > Match assumed.
Progress(ma,ne,ac) == [match |-> ma, next |-> ne, mode |-> "Probe",
                      probe |-> FALSE, pending |-> 0, active |-> ac, inflight |-> <<>>,
                      evidence |-> <<>>]
ResetProgress(p,mode) == [p EXCEPT !.mode=mode, !.probe=FALSE,
                                !.pending=0, !.inflight= <<>>]
BecomeProbe(p) == [ResetProgress(p,"Probe") EXCEPT
    !.next = IF p.mode="Snapshot" THEN Max(p.match+1,p.pending+1) ELSE p.match+1]
BecomeReplicate(p) == [ResetProgress(p,"Replicate") EXCEPT !.next=p.match+1]
Paused(p) == CASE p.mode="Probe" -> p.probe
              [] p.mode="Replicate" -> Len(p.inflight)>=MaxInflight
              [] OTHER -> TRUE
MaybeUpdate(p,n,h) == [p EXCEPT !.match=Max(@,n), !.next=Max(@,n+1),
    !.probe=IF n>p.match THEN FALSE ELSE @,
    !.evidence=IF n>p.match THEN h ELSE @]
FreeLE(p,n) == [p EXCEPT !.inflight=SelectSeq(@,LAMBDA x: x>n)]
Decreases(p,rejected) == IF p.mode="Replicate" THEN rejected>p.match
                        ELSE p.next-1=rejected
MaybeDecrTo(p,rejected,hint) ==
    IF ~Decreases(p,rejected) THEN p
    ELSE IF p.mode="Replicate" THEN BecomeProbe([p EXCEPT !.next=p.match+1])
    ELSE [p EXCEPT !.next=Max(1,Min(rejected,hint+1)), !.probe=FALSE]

\* log.go:177-251, log_unstable.go:33-75; full prefixes below cut are ghosts.
Hist(r) == IF r.unstable # <<>> THEN
              Prefix(IF r.usnap.index>0 THEN r.usnap.hist ELSE r.store.hist,r.uoff-1)
                \o r.unstable
           ELSE IF r.usnap.index>0 THEN r.usnap.hist ELSE r.store.hist
Last(r) == Len(Hist(r))
First(r) == IF r.usnap.index>0 THEN r.usnap.index+1 ELSE r.store.cut+1
Term(r,i) == IF i<First(r)-1 \/ i>Last(r) \/ i=0 THEN 0 ELSE Hist(r)[i].term
Matches(r,i,t) == Term(r,i)=t
UpToDate(r,i,t) == t>Term(r,Last(r)) \/ (t=Term(r,Last(r)) /\ i>=Last(r))
HS(r) == [term |-> r.term, vote |-> r.vote, commit |-> r.commit]
SS(r) == [role |-> r.role, lead |-> r.lead]
\* quorum/joint.go:28-75; tracker/tracker.go:144-187.
VoterIDs(cfg) == cfg.voters \cup cfg.outgoing
Members(r) == VoterIDs(r.config) \cup r.config.learners
Promotable(r) == r.id \in VoterIDs(r.config) /\ r.id \notin r.config.learners
\* quorum/majority.go:170-201 includes empty-set win and even-sized loss.
Won(voters,yes) == voters={} \/ Cardinality(voters \cap yes)>Cardinality(voters)\div 2
Lost(voters,yes,no) == ~Won(voters,yes) /\
    Cardinality(voters \ no)<=Cardinality(voters)\div 2
JointWon(cfg,yes) == Won(cfg.voters,yes) /\ Won(cfg.outgoing,yes)
JointLost(cfg,yes,no) == Lost(cfg.voters,yes,no) \/ Lost(cfg.outgoing,yes,no)
IsSingleton(cfg) == Cardinality(cfg.voters)=1 /\ cfg.outgoing={}
QuorumIndex(r) == IF r.config.voters={} THEN Last(r)+1 ELSE
    MaxSet({i \in 0..Last(r): JointWon(r.config,
                          {n \in VoterIDs(r.config):r.prs[n].match>=i})})
Fatal(r,reason) == [r EXCEPT !.fatal=reason]
\* log.go:199-217; errors are results, not enabling restrictions.
CommitTo(r,i) == IF i<=r.commit THEN r
                 ELSE IF i>Last(r) THEN Fatal(r,"commit beyond lastIndex")
                 ELSE [r EXCEPT !.commit=i]
AppliedTo(r,i) == IF i=0 THEN r
    ELSE IF i<r.applied \/ i>r.commit THEN Fatal(r,"appliedTo bounds")
    ELSE [r EXCEPT !.applied=i]
MaybeCommit(r) == LET i==QuorumIndex(r) IN
    IF i>r.commit /\ Term(r,i)=r.term THEN
        [CommitTo(r,i) EXCEPT !.commitUses=@\cup
          {[hist |-> Prefix(Hist(r),i), config |-> r.config,
            term |-> r.term, oldCommit |-> r.commit,
            matches |-> {n\in VoterIDs(r.config):r.prs[n].match>=i}]}] ELSE r
\* log_unstable.go:123-142, log.go:106-114; preserve unstable replacement.
AppendLog(r,es) == IF es= <<>> THEN r ELSE
    IF Head(es).index-1<r.commit THEN Fatal(r,"append below committed") ELSE
    [r EXCEPT !.unstable=IF Head(es).index<=r.uoff THEN es
                         ELSE Prefix(@,Head(es).index-r.uoff) \o es,
               !.uoff=Min(@,Head(es).index)]

\* S5 read witnesses are attached by observation, not used in branch guards.
EmptyRead == [id |-> 0, rid |-> 0, requester |-> 0, index |-> 0, term |-> 0,
              leader |-> 0, config |-> EmptyConfig, acks |-> {},
              hist |-> <<>>, confirmConfig |-> EmptyConfig, confirmAcks |-> {},
              confirmTerm |-> 0, singleton |-> FALSE]
Message(ty,fr,to,t) == [type |-> ty, from |-> fr, to |-> to, term |-> t,
    index |-> 0, logTerm |-> 0, commit |-> 0, entries |-> <<>>,
    reject |-> FALSE, hint |-> 0, context |-> 0, snapshot |-> EmptySnapshot,
    request |-> 0, witness |-> <<>>, read |-> EmptyRead, forced |-> FALSE]
Send(r,m) == [r EXCEPT !.out=AddBag(@,m)]
\* raft.go:565-594; reset leaves log, readStates, outgoing messages intact.
Reset(r,t,timeout) == [r EXCEPT
    !.term=t, !.vote=IF t#r.term THEN 0 ELSE @, !.lead=0,
    !.elapsed=0, !.heartbeat=0, !.timeout=timeout, !.transfer=0,
    !.yes={}, !.no={}, !.pendingConf=0, !.quota=0, !.readQueue= <<>>,
    !.prs=[n \in Members(r) |-> Progress(IF n=r.id THEN Last(r) ELSE 0,Last(r)+1,FALSE)]]
BecomeFollower(r,t,leader,timeout) ==
    [Reset(r,t,timeout) EXCEPT !.role="Follower", !.lead=leader]
\* raft.go:596-616; self Match is volatile, payload quota permits oversized first.
AppendQuotaExceeded(r,es) == r.quota>0 /\ r.quota+Weight(es)>MaxUncommitted
AppendEntry(r,es) == LET fixed==[k \in DOMAIN es |->
                                     [es[k] EXCEPT !.term=r.term, !.index=Last(r)+k]] IN
    IF AppendQuotaExceeded(r,es)
    THEN [r EXCEPT !.decision="DropQuota"]
    ELSE LET a==AppendLog([r EXCEPT !.quota=@+Weight(es)],fixed)
             b==[a EXCEPT !.prs[r.id]=MaybeUpdate(@,Last(a),Hist(a))]
         IN MaybeCommit(b)
\* raft.go:730-764. Record both joint halves at the actual election before reset.
BecomeLeader(r,timeout) ==
    IF r.role="Follower" THEN Fatal(r,"follower to leader")
    ELSE IF r.id \notin DOMAIN r.prs THEN Fatal(r,"leader missing self progress")
    ELSE LET win==[node |-> r.id, term |-> r.term, hist |-> Hist(r),
                   config |-> r.config, yes |-> r.yes]
             a==[Reset(r,r.term,timeout) EXCEPT !.role="Leader", !.lead=r.id,
                 !.pendingConf=Last(r), !.wins=@ \cup {win},
                 !.prs[r.id]=BecomeReplicate(@)]
         IN AppendEntry(a,<<Entry(0,0,"Normal",0,0,0,EmptyEncoded)>>)

\* raft.go:445-504; each invocation preserves empty/nonempty, pause, snapshot paths.
MaybeSendAppend(r,to,sendEmpty) ==
    LET p==r.prs[to] IN
    IF r.fatal#"" \/ Paused(p) THEN r ELSE
    \* Compacted entries return nil+ErrCompacted, not the retained ghost prefix
    \* (log.go:306-310,347-356). The empty-refill return precedes snapshot fallback.
    LET es==IF p.next<First(r) \/ p.next>Last(r) THEN <<>> ELSE
                  LimitSize(Suffix(Hist(r),p.next),MaxMsgSize)
    IN IF es= <<>> /\ ~sendEmpty THEN r
       ELSE IF p.next<First(r) THEN
           \* log.go:170-174 prefers an unstable snapshot over Storage.Snapshot.
           IF ~p.active \/ (r.usnap.index=0 /\ ~r.snapAvailable) THEN r
           ELSE LET snap==IF r.usnap.index>0 THEN r.usnap ELSE r.store.snapshot IN
                IF snap.index=0 THEN Fatal(r,"need non-empty snapshot") ELSE
                Send([r EXCEPT !.prs[to]=[ResetProgress(p,"Snapshot") EXCEPT !.pending=snap.index]],
                     [Message("MsgSnap",r.id,to,r.term) EXCEPT !.snapshot=snap])
       ELSE IF p.next>Last(r)+1 THEN Fatal(r,"append next out of bounds")
       ELSE LET p2==IF es= <<>> THEN p
                    ELSE IF p.mode="Replicate" THEN [p EXCEPT
                         !.next=es[Len(es)].index+1, !.inflight=Append(@,es[Len(es)].index)]
                    ELSE [p EXCEPT !.probe=TRUE]
                msg==[Message("MsgApp",r.id,to,r.term) EXCEPT
                     !.index=p.next-1, !.logTerm=Term(r,p.next-1), !.entries=es,
                     !.commit=r.commit, !.witness=Hist(r)]
            IN Send([r EXCEPT !.prs[to]=p2],msg)
\* raft.go:1078-1084; finite recursion sends all allowed nonempty batches atomically.
RECURSIVE FillAppend(_, _)
FillAppend(r,to) == LET a==MaybeSendAppend(r,to,FALSE) IN
    IF a=r \/ a.fatal#"" THEN a ELSE FillAppend(a,to)
RECURSIVE BroadcastAppend(_, _), BroadcastHeartbeat(_, _, _), BroadcastVotes(_, _, _, _)
BroadcastAppend(r,peers) == IF peers={} THEN r ELSE
    LET n==CHOOSE x \in peers:TRUE IN BroadcastAppend(MaybeSendAppend(r,n,TRUE),peers\{n})
BcastAppend(r) == BroadcastAppend(r,Members(r)\{r.id})
\* raft.go:508-554; heartbeat commit is capped by peer Match.
BroadcastHeartbeat(r,peers,ctx) == IF peers={} THEN r ELSE
    LET n==CHOOSE x \in peers:TRUE
        m==[Message("MsgHeartbeat",r.id,n,r.term) EXCEPT
             !.commit=Min(r.prs[n].match,r.commit), !.context=ctx, !.witness=Hist(r)]
    IN BroadcastHeartbeat(Send(r,m),peers\{n},ctx)
BcastHeartbeat(r,ctx) == BroadcastHeartbeat(r,Members(r)\{r.id},ctx)
LastContext(r) == IF r.readQueue= <<>> THEN 0 ELSE r.readQueue[Len(r.readQueue)].id
\* raft.go:766-808; vote requests go to the union of both joint voter halves.
BroadcastVotes(r,peers,pre,forced) == IF peers={} THEN r ELSE
    LET n==CHOOSE x \in peers:TRUE
        m==[Message(IF pre THEN "MsgPreVote" ELSE "MsgVote",r.id,n,
                    IF pre THEN r.term+1 ELSE r.term) EXCEPT
            !.index=Last(r), !.logTerm=Term(r,Last(r)), !.forced=forced]
    IN BroadcastVotes(Send(r,m),peers\{n},pre,forced)
CampaignElection(r,forced,timeout) ==
    IF r.role="Leader" THEN Fatal(r,"leader to candidate") ELSE
    LET a==[Reset(r,r.term+1,timeout) EXCEPT !.role="Candidate", !.vote=r.id, !.yes={r.id},
             !.campaigns=@ \cup {[node |-> r.id, learner |-> r.id\in r.config.learners]}]
    IN IF JointWon(a.config,a.yes) THEN BecomeLeader(a,timeout)
       ELSE BroadcastVotes(a,VoterIDs(a.config)\{a.id},FALSE,forced)
CampaignPreElection(r,timeout) ==
    IF r.role="Leader" THEN Fatal(r,"leader to pre-candidate") ELSE
    LET a==[r EXCEPT !.role="PreCandidate", !.lead=0, !.yes={r.id}, !.no={},
             !.campaigns=@ \cup {[node |-> r.id, learner |-> r.id\in r.config.learners]}]
    IN IF JointWon(a.config,a.yes) THEN CampaignElection(a,FALSE,timeout)
       ELSE BroadcastVotes(a,VoterIDs(a.config)\{a.id},TRUE,FALSE)
\* raft.go:859-883 and log.go:347-359. Do not clamp the Hup scan to First.
StepHup(r,timeout) ==
    IF r.role="Leader" \/ ~Promotable(r) THEN r
    ELSE IF r.applied+1<First(r) THEN Fatal(r,"Hup unapplied slice compacted")
    ELSE IF \E k \in (r.applied+1)..r.commit: Hist(r)[k].kind\in LegacyConfKinds THEN r
    ELSE IF r.preVote THEN CampaignPreElection(r,timeout)
         ELSE CampaignElection(r,FALSE,timeout)

\* raft.go:924-972. A learner may grant when the ordinary vote and log checks
\* pass, but still cannot campaign (StepHup/Promotable). Candidate membership is
\* not tested here; the candidate counts the response under its own config.
\* UPDATE-MAP
\* code: raft.go:Step MsgVote/MsgPreVote
\* update: Update!AffectedElectionActions
StepVote(r,m) ==
    LET can==r.vote=m.from \/ (r.vote=0 /\ r.lead=0) \/
             (m.type="MsgPreVote" /\ m.term>r.term)
        grant==can /\ UpToDate(r,m.index,m.logTerm)
        ty==IF m.type="MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp"
        a==IF grant /\ m.type="MsgVote" THEN [r EXCEPT !.vote=m.from, !.elapsed=0]
           ELSE r
        b==IF grant THEN [a EXCEPT !.grants=@ \cup
             {[node |-> r.id, learner |-> r.id\in r.config.learners,
               term |-> m.term, candidate |-> m.from, pre |-> m.type="MsgPreVote"]}]
           ELSE a
    IN Send(b,[Message(ty,r.id,m.from,IF grant THEN m.term ELSE r.term) EXCEPT !.reject=~grant])
\* raft.go:1291-1303; log.go:88-103; compare terms, not symbolic payload identity.
HandleAppendEntries(r,m) ==
    IF m.index<r.commit THEN
        Send(r,[Message("MsgAppResp",r.id,m.from,r.term) EXCEPT
                 !.index=r.commit, !.witness=Prefix(Hist(r),r.commit)])
    ELSE IF ~Matches(r,m.index,m.logTerm) THEN
        Send(r,[Message("MsgAppResp",r.id,m.from,r.term) EXCEPT
                 !.index=m.index, !.reject=TRUE, !.hint=Last(r)])
    ELSE LET conflicts=={k \in DOMAIN m.entries:
                           ~Matches(r,m.entries[k].index,m.entries[k].term)}
             first==IF conflicts={} THEN 0 ELSE MinSet(conflicts)
             a==IF first=0 THEN r
                ELSE IF m.entries[first].index<=r.commit THEN Fatal(r,"conflict with committed entry")
                ELSE AppendLog(r,Suffix(m.entries,first))
             lastNew==m.index+Len(m.entries)
             b==IF a.fatal#"" THEN a ELSE CommitTo(a,Min(m.commit,lastNew))
         IN IF b.fatal#"" THEN b ELSE Send(b,
            [Message("MsgAppResp",r.id,m.from,r.term) EXCEPT
             !.index=lastNew, !.witness=Prefix(Hist(b),lastNew)])
\* raft.go:1306-1308: cap is in sender; receiver directly attempts commitTo.
HandleHeartbeat(r,m) == LET a==CommitTo(r,m.commit) IN
    IF a.fatal#"" THEN a ELSE Send(a,
       [Message("MsgHeartbeatResp",r.id,m.from,r.term) EXCEPT !.context=m.context])
\* confchange/restore.go:22-154; raft.go:newRaft,restore. Revision 46580dcf
\* reconstructs the complete ConfState atomically. The preceding live-snapshot
\* membership guard still checks only incoming voters and current learners.
\* UPDATE-MAP
\* code: confchange/restore.go:Restore; raft.go:newRaft,restore
\* update: Update!AffectedRecoveryActions
RestoreProjection(cfg) == cfg
Restore(r,s,timeout) ==
    IF s.index<=r.commit THEN r
    ELSE IF r.role#"Follower" THEN BecomeFollower(r,r.term+1,0,timeout)
    ELSE IF r.id\notin s.config.voters\cup s.config.learners THEN r
    ELSE IF Matches(r,s.index,s.term) THEN CommitTo(r,s.index)
    ELSE LET cfg==RestoreProjection(s.config) IN
         [r EXCEPT !.commit=s.index, !.usnap=s, !.unstable= <<>>, !.uoff=s.index+1,
           !.config=cfg, !.cfgHist=s.hist,
           !.yes={}, !.no={},
           !.prs=[n \in VoterIDs(cfg)\cup cfg.learners |->
                     Progress(IF n=r.id THEN s.index ELSE 0,s.index+1,TRUE)]]
HandleSnapshot(r,m,timeout) == LET a==Restore(r,m.snapshot,timeout) IN
    Send(a,[Message("MsgAppResp",r.id,m.from,a.term) EXCEPT
            !.index=IF a.usnap=m.snapshot /\ m.snapshot.index>r.commit THEN Last(a) ELSE a.commit,
            !.witness=Prefix(Hist(a),a.commit)])

\* raft.go:999-1030; both legacy and V2 entries share pending-conf admission.
RECURSIVE RewriteConf(_,_,_)
RewriteConf(r,es,k) == IF k>Len(es) THEN [state |-> r, entries |-> es] ELSE
    IF es[k].kind\notin ConfKinds THEN RewriteConf(r,es,k+1)
    ELSE IF r.pendingConf>r.applied THEN
        RewriteConf(r,[es EXCEPT ![k]=Entry(0,0,"Normal",0,0,0,EmptyEncoded)],k+1)
    ELSE RewriteConf([r EXCEPT !.pendingConf=Last(r)+k],es,k+1)
\* raft.go:962-994; preserve admission, rewrite, quota drop as observations.
StepLeaderProposal(r,m) ==
    IF m.entries= <<>> THEN Fatal(r,"empty proposal")
    ELSE IF r.id\notin Members(r) THEN [r EXCEPT !.decision="DropRemoved"]
    ELSE IF r.transfer#0 THEN [r EXCEPT !.decision="DropTransfer"]
    ELSE LET rw==RewriteConf(r,m.entries,1)
             a==AppendEntry([rw.state EXCEPT !.decision="Accepted"],rw.entries)
         IN IF a.decision="DropQuota" THEN a ELSE BcastAppend(a)
\* raft.go:1032-1064, read_only.go:56-75. Context id 0 denotes empty bytes.
ReadRecord(r,m) == [EmptyRead EXCEPT !.id=m.context, !.rid=m.request, !.requester=m.from,
    !.index=r.commit, !.term=r.term, !.leader=r.id, !.config=r.config,
    !.acks={r.id}, !.hist=Prefix(Hist(r),r.commit)]
DeliverReadState(r,rd) == IF rd.requester\in {0,r.id}
    THEN [r EXCEPT !.readStates=Append(@,rd)]
    ELSE Send(r,[Message("MsgReadIndexResp",r.id,rd.requester,r.term) EXCEPT
          !.index=rd.index, !.context=rd.id, !.request=rd.id, !.read=rd])
StepLeaderReadIndex(r,m) ==
    IF IsSingleton(r.config) THEN
        DeliverReadState(r,[ReadRecord(r,m) EXCEPT !.singleton=TRUE,
            !.confirmConfig=r.config, !.confirmAcks={r.id}, !.confirmTerm=r.term])
    ELSE IF Term(r,r.commit)#r.term THEN r
    ELSE LET exists==\E k \in DOMAIN r.readQueue:r.readQueue[k].id=m.context
             a==IF exists THEN r ELSE [r EXCEPT !.readQueue=Append(@,ReadRecord(r,m))]
         IN BcastHeartbeat(a,m.context)
\* raft.go:1137-1158; a later context releases a prefix under CURRENT joint voters.
RECURSIVE ReleaseReadPrefix(_,_,_,_,_)
ReleaseReadPrefix(r,qs,cfg,acks,t) == IF qs= <<>> THEN r ELSE
    ReleaseReadPrefix(DeliverReadState(r,[Head(qs) EXCEPT !.confirmConfig=cfg,
                        !.confirmAcks=acks, !.confirmTerm=t]),Tail(qs),cfg,acks,t)
ReadOnlyRecvAck(r,m) ==
    LET ks=={k \in DOMAIN r.readQueue:r.readQueue[k].id=m.context} IN
    IF m.context=0 \/ ks={} THEN r ELSE
    LET k==MinSet(ks)
        a==[r EXCEPT !.readQueue[k].acks=@\cup {m.from}]
        acks==a.readQueue[k].acks
    IN IF ~JointWon(a.config,acks) THEN a ELSE
       ReleaseReadPrefix([a EXCEPT !.readQueue=Suffix(@,k+1)],
                         Prefix(a.readQueue,k),a.config,acks,a.term)
\* raft.go:1039-1091; MaybeUpdate always raises Next, even if Match did not change.
StepLeaderAppResp(r,m) ==
    LET p==[r.prs[m.from] EXCEPT !.active=TRUE]
        a==[r EXCEPT !.prs[m.from]=p]
    IN IF m.reject THEN
        IF Decreases(p,m.index) THEN
            MaybeSendAppend([a EXCEPT !.prs[m.from]=MaybeDecrTo(p,m.index,m.hint)],m.from,TRUE)
        ELSE a
       ELSE LET p2==MaybeUpdate(p,m.index,m.witness)
                b==[a EXCEPT !.prs[m.from]=p2]
            IN IF m.index<=p.match THEN b ELSE
               LET p3==IF p2.mode="Probe" THEN BecomeReplicate(p2)
                       ELSE IF p2.mode="Snapshot" /\ p2.match>=p2.pending
                            THEN BecomeReplicate(BecomeProbe(p2))
                       ELSE IF p2.mode="Replicate" THEN FreeLE(p2,m.index) ELSE p2
                   c==MaybeCommit([b EXCEPT !.prs[m.from]=p3])
                   d==IF c.commit>b.commit THEN BcastAppend(c)
                      ELSE IF Paused(p) THEN MaybeSendAppend(c,m.from,TRUE) ELSE c
                   e==FillAppend(d,m.from)
               IN IF m.from=e.transfer /\ e.prs[m.from].match=Last(e)
                  THEN Send(e,Message("MsgTimeoutNow",e.id,m.from,e.term)) ELSE e
\* raft.go:1093-1103; heartbeat quota release does not advance Match.
StepLeaderHeartbeatResp(r,m) ==
    LET p==[r.prs[m.from] EXCEPT !.active=TRUE, !.probe=FALSE]
        p2==IF p.mode="Replicate" /\ Len(p.inflight)>=MaxInflight
            THEN [p EXCEPT !.inflight=Tail(@)] ELSE p
        a==[r EXCEPT !.prs[m.from]=p2]
        b==IF p2.match<Last(a) THEN MaybeSendAppend(a,m.from,TRUE) ELSE a
    IN ReadOnlyRecvAck(b,m)
\* raft.go:1122-1143; successful transport is not a replication acknowledgment.
StepLeaderSnapStatus(r,m) == IF r.prs[m.from].mode#"Snapshot" THEN r ELSE
    LET p==IF m.reject THEN [r.prs[m.from] EXCEPT !.pending=0] ELSE r.prs[m.from]
    IN [r EXCEPT !.prs[m.from]=[BecomeProbe(p) EXCEPT !.probe=TRUE]]
\* raft.go:1151-1181; same-target ignore, replacement abort, then self check.
StepLeaderTransfer(r,m) ==
    IF m.from\in r.config.learners \/ r.transfer=m.from THEN r
    ELSE LET a==[r EXCEPT !.transfer=0] IN
         IF m.from=r.id THEN a ELSE
         LET b==[a EXCEPT !.transfer=m.from, !.elapsed=0] IN
         IF b.prs[m.from].match=Last(b)
         THEN Send(b,Message("MsgTimeoutNow",r.id,m.from,r.term))
         ELSE MaybeSendAppend(b,m.from,TRUE)
\* raft.go:977-998 and tracker/tracker.go:176-187; active requires both majorities.
StepCheckQuorum(r,timeout) ==
    LET a==IF r.id\in Members(r) THEN [r EXCEPT !.prs[r.id].active=TRUE] ELSE r
        active=={n \in VoterIDs(a.config):a.prs[n].active}
        b==IF JointWon(a.config,active) THEN a ELSE BecomeFollower(a,a.term,0,timeout)
    IN [b EXCEPT !.prs=[n \in Members(b) |->
                         IF n=b.id THEN b.prs[n] ELSE [b.prs[n] EXCEPT !.active=FALSE]]]
StepLeader(r,m,timeout) ==
    CASE m.type="MsgBeat" -> BcastHeartbeat(r,LastContext(r))
      [] m.type="MsgCheckQuorum" -> StepCheckQuorum(r,timeout)
      [] m.type="MsgProp" -> StepLeaderProposal(r,m)
      [] m.type="MsgReadIndex" -> StepLeaderReadIndex(r,m)
      [] m.from\notin Members(r) -> r
      [] m.type="MsgAppResp" -> StepLeaderAppResp(r,m)
      [] m.type="MsgHeartbeatResp" -> StepLeaderHeartbeatResp(r,m)
      [] m.type="MsgSnapStatus" -> StepLeaderSnapStatus(r,m)
      [] m.type="MsgUnreachable" -> IF r.prs[m.from].mode="Replicate"
              THEN [r EXCEPT !.prs[m.from]=BecomeProbe(@)] ELSE r
      [] m.type="MsgTransferLeader" -> StepLeaderTransfer(r,m)
      [] OTHER -> r
\* raft.go:1188-1230; first recorded vote wins; empty-voter helper remains reachable.
StepCandidate(r,m,timeout) ==
    CASE m.type="MsgProp" -> [r EXCEPT !.decision="DropNoLeader"]
      [] m.type="MsgApp" -> HandleAppendEntries(BecomeFollower(r,m.term,m.from,timeout),m)
      [] m.type="MsgHeartbeat" -> HandleHeartbeat(BecomeFollower(r,m.term,m.from,timeout),m)
      [] m.type="MsgSnap" -> HandleSnapshot(BecomeFollower(r,m.term,m.from,timeout),m,timeout)
      [] m.type=(IF r.role="PreCandidate" THEN "MsgPreVoteResp" ELSE "MsgVoteResp") ->
         LET a==IF m.from\in r.yes\cup r.no THEN r
                ELSE IF m.reject THEN [r EXCEPT !.no=@\cup {m.from}]
                ELSE [r EXCEPT !.yes=@\cup {m.from}]
         IN IF JointWon(a.config,a.yes) THEN
                IF a.role="PreCandidate" THEN CampaignElection(a,FALSE,timeout)
                ELSE BcastAppend(BecomeLeader(a,timeout))
            ELSE IF JointLost(a.config,a.yes,a.no) THEN BecomeFollower(a,a.term,0,timeout)
            ELSE a
      [] OTHER -> r
\* raft.go:1233-1287. TimeoutNow intentionally skips the Hup configuration scan.
StepFollower(r,m,timeout) ==
    CASE m.type="MsgProp" -> IF r.lead=0 THEN [r EXCEPT !.decision="DropNoLeader"]
                ELSE IF r.noForward THEN [r EXCEPT !.decision="DropForwardDisabled"]
                ELSE Send([r EXCEPT !.decision="Forwarded"],[m EXCEPT !.from=r.id, !.to=r.lead])
      [] m.type="MsgApp" -> HandleAppendEntries([r EXCEPT !.elapsed=0, !.lead=m.from],m)
      [] m.type="MsgHeartbeat" -> HandleHeartbeat([r EXCEPT !.elapsed=0, !.lead=m.from],m)
      [] m.type="MsgSnap" -> HandleSnapshot([r EXCEPT !.elapsed=0, !.lead=m.from],m,timeout)
      [] m.type="MsgTransferLeader" -> IF r.lead=0 THEN r ELSE Send(r,[m EXCEPT !.from=r.id, !.to=r.lead])
      [] m.type="MsgTimeoutNow" -> IF Promotable(r) THEN CampaignElection(r,TRUE,timeout) ELSE r
      [] m.type="MsgReadIndex" -> IF r.lead=0 THEN r ELSE Send(r,[m EXCEPT !.from=r.id, !.to=r.lead])
      [] m.type="MsgReadIndexResp" -> [r EXCEPT !.readStates=Append(@,m.read)]
      [] OTHER -> r
\* raft.go:784-929. Higher-term PreVote exceptions precede role dispatch.
StepDispatch(r,m,timeout) ==
    CASE m.type="MsgHup" -> StepHup(r,timeout)
      [] m.type\in {"MsgVote","MsgPreVote"} -> StepVote(r,m)
      [] r.role="Leader" -> StepLeader(r,m,timeout)
      [] r.role\in {"Candidate","PreCandidate"} -> StepCandidate(r,m,timeout)
      [] OTHER -> StepFollower(r,m,timeout)
Step(r,m,timeout) ==
    IF m.term>r.term /\ m.type\in {"MsgVote","MsgPreVote"} /\
       ~m.forced /\ r.checkQuorum /\ r.lead#0 /\ r.elapsed<ElectionTick THEN r
    ELSE IF m.term#0 /\ m.term<r.term THEN
        IF (r.checkQuorum \/ r.preVote) /\ m.type\in {"MsgHeartbeat","MsgApp"}
        THEN Send(r,Message("MsgAppResp",r.id,m.from,r.term))
        ELSE IF m.type="MsgPreVote" THEN
             Send(r,[Message("MsgPreVoteResp",r.id,m.from,r.term) EXCEPT !.reject=TRUE]) ELSE r
    ELSE LET a==IF m.term>r.term /\ m.type#"MsgPreVote" /\
                   ~(m.type="MsgPreVoteResp" /\ ~m.reject)
                THEN BecomeFollower(r,m.term,
                       IF m.type\in {"MsgApp","MsgHeartbeat","MsgSnap"} THEN m.from ELSE 0,timeout)
                ELSE r
         IN StepDispatch(a,m,timeout)
\* raft.go:619-653; tick includes all triggered core work within one call.
TickCore(r,timeout) ==
    IF r.role#"Leader" THEN
       LET a==[r EXCEPT !.elapsed=@+1] IN
       IF Promotable(a) /\ a.elapsed>=a.timeout THEN StepHup([a EXCEPT !.elapsed=0],timeout) ELSE a
    ELSE LET a==[r EXCEPT !.elapsed=@+1, !.heartbeat=@+1]
             b==IF a.elapsed>=ElectionTick THEN
                  IF a.checkQuorum THEN StepCheckQuorum([a EXCEPT !.elapsed=0],timeout)
                  ELSE [a EXCEPT !.elapsed=0]
                ELSE a
             c==IF a.elapsed>=ElectionTick /\ b.role="Leader" THEN [b EXCEPT !.transfer=0] ELSE b
         IN IF c.role="Leader" /\ c.heartbeat>=HeartbeatTick
            THEN BcastHeartbeat([c EXCEPT !.heartbeat=0],LastContext(c)) ELSE c

\* confchange/confchange.go:49-152,155-276 and raftpb/confchange.go:69-104.
\* These pure operators are the independently reviewable joint-config oracle.
RECURSIVE ApplyChanges(_, _)
ApplySingle(cfg,ch) ==
    IF ch.target=0 THEN cfg ELSE
    CASE ch.kind="AddVoter" ->
           [cfg EXCEPT !.voters=@\cup {ch.target},
                       !.learners=@\{ch.target}, !.learnersNext=@\{ch.target}]
      [] ch.kind="AddLearner" ->
           IF ch.target\in cfg.learners THEN cfg ELSE
           LET a==[cfg EXCEPT !.voters=@\{ch.target},
                              !.learners=@\{ch.target}, !.learnersNext=@\{ch.target}]
           IN IF ch.target\in cfg.outgoing
              THEN [a EXCEPT !.learnersNext=@\cup {ch.target}]
              ELSE [a EXCEPT !.learners=@\cup {ch.target}]
      [] ch.kind="Remove" ->
           [cfg EXCEPT !.voters=@\{ch.target},
                       !.learners=@\{ch.target}, !.learnersNext=@\{ch.target}]
      [] OTHER -> cfg
ApplyChanges(cfg,changes) ==
    IF changes= <<>> THEN cfg ELSE ApplyChanges(ApplySingle(cfg,Head(changes)),Tail(changes))
\* Behavior repair R1: raftpb/confchange.go:103-107 requires zero Transition.
IsLeave(e) == e.kind="V2" /\ e.changes= <<>> /\ e.transition="Auto"
EntersJoint(e) == e.kind="V2" /\ ~IsLeave(e) /\
                  (e.transition#"Auto" \/ Len(e.changes)>1)
AutoLeaves(e) == EntersJoint(e) /\ e.transition\in {"Auto","JointImplicit"}
CanceledEntry(e) == e.kind#"V2" /\ e.id\in CancelChanges
ConfigCandidate(cfg,e) ==
    IF e.kind\notin ConfKinds \/ CanceledEntry(e) THEN cfg
    ELSE IF IsLeave(e) THEN
        [cfg EXCEPT !.outgoing={}, !.learners=@\cup cfg.learnersNext,
                    !.learnersNext={}, !.autoLeave=FALSE]
    ELSE IF EntersJoint(e) THEN
        ApplyChanges([cfg EXCEPT !.outgoing=cfg.voters,
                                 !.autoLeave=AutoLeaves(e)],e.changes)
    ELSE ApplyChanges(cfg,e.changes)
ConfigWellFormed(cfg) ==
    /\ cfg.voters#{}
    /\ cfg.voters\subseteq Server /\ cfg.outgoing\subseteq Server
    /\ cfg.learners\subseteq Server /\ cfg.learnersNext\subseteq Server
    /\ cfg.learners\cap VoterIDs(cfg)={}
    /\ cfg.learnersNext\subseteq cfg.outgoing
    /\ cfg.learnersNext\cap (cfg.voters\cup cfg.learners)={}
    /\ (cfg.outgoing={} => cfg.learnersNext={} /\ ~cfg.autoLeave)
VoterDifference(a,b) == (a\b)\cup(b\a)
ValidConfigTransition(cfg,e) ==
    LET after==ConfigCandidate(cfg,e) IN
    /\ e.kind\in ConfKinds
    /\ ConfigWellFormed(after)
    /\ CASE IsLeave(e) -> cfg.outgoing#{}
          [] EntersJoint(e) -> cfg.outgoing={} /\ cfg.voters#{}
          [] OTHER -> cfg.outgoing={} /\
                      Cardinality(VoterDifference(cfg.voters,after.voters))<=1
ConfigAfter(cfg,e) == IF e.kind\notin ConfKinds THEN cfg ELSE
    IF ValidConfigTransition(cfg,e) THEN ConfigCandidate(cfg,e) ELSE cfg
RECURSIVE ConfigOf(_)
ConfigOf(h) == IF h= <<>> THEN EmptyConfig ELSE ConfigAfter(ConfigOf(Prefix(h,Len(h)-1)),h[Len(h)])
\* Local repair: preserve intermediate Changer Progress deletion/recreation.
RECURSIVE ChangeProgress(_,_,_,_)
ChangeProgress(cfg,prs,last,changes) == IF changes= <<>> THEN prs ELSE
 LET nextCfg==ApplySingle(cfg,Head(changes))
     nextPrs==[n \in VoterIDs(nextCfg)\cup nextCfg.learners |->
         IF n \in DOMAIN prs THEN prs[n] ELSE Progress(0,last+1,TRUE)]
 IN ChangeProgress(nextCfg,nextPrs,last,Tail(changes))
ApplyConfCore(r,e,timeout) ==
    LET cfg==ConfigCandidate(r.config,e)
        members==VoterIDs(cfg)\cup cfg.learners
        a==IF ~ValidConfigTransition(r.config,e)
           THEN Fatal(r,"invalid configuration transition") ELSE
           LET startCfg==IF EntersJoint(e) THEN [r.config EXCEPT !.outgoing=r.config.voters] ELSE r.config
               changed==IF IsLeave(e) \/ CanceledEntry(e) THEN r.prs ELSE
                            ChangeProgress(startCfg,r.prs,Last(r),e.changes)
           IN [r EXCEPT !.config=cfg, !.prs=[n \in members |-> changed[n]]]
    IN IF a.fatal#"" \/ r.role#"Leader" \/ ~Promotable(a) \/ cfg.voters={} THEN a ELSE
       LET b==MaybeCommit(a)
           c==IF b.commit>a.commit THEN BcastAppend(b) ELSE b
       IN IF c.fatal#"" THEN c ELSE IF c.transfer#0 /\ c.transfer\notin members THEN [c EXCEPT !.transfer=0] ELSE c

(***************************************************************************
Caller, storage and observation layer: S1/S3/S4/S5/S6.
Environment boundaries cite interface contracts; they are not Raft internals.
***************************************************************************)
EmptyFunction == [x \in {} |-> 0]
Override(f,g) == [x \in DOMAIN f\cup DOMAIN g |-> IF x\in DOMAIN g THEN g[x] ELSE f[x]]
MissingEntry(k) == Entry(0,k,"Missing",0,0,0,1)
DiskHist(d) == [k \in 1..Max(d.snapshot.index,MaxSet(DOMAIN d.log)) |->
    IF k<=d.snapshot.index THEN d.snapshot.hist[k]
    ELSE IF k\in DOMAIN d.log THEN d.log[k] ELSE MissingEntry(k)]
DiskHas(d,h) == Covers(DiskHist(d),h)
EmptyDisk == [hs |-> EmptyHS, log |-> EmptyFunction, snapshot |-> EmptySnapshot,
              savedApp |-> <<>>]
Store(h,s,cut,hs) == [hist |-> h, snapshot |-> s, cut |-> cut, hs |-> hs]
\* README.md:116,124. No torn HardState. Disk completion and Storage view differ.
DiskAppend(d,es) == IF es= <<>> THEN d ELSE
    [d EXCEPT !.log=Override([k \in {x\in DOMAIN d.log:x<Head(es).index} |-> d.log[k]],
                             [k \in {e.index:e\in SeqSet(es)} |->
                                      es[k-Head(es).index+1]])]
\* storage.go:239-269, caller uses ApplySnapshot before Append in Storage view.
StoreAppend(st,es) == IF es= <<>> THEN st ELSE
    LET tail==SelectSeq(es,LAMBDA e:e.index>st.cut) IN
    IF tail= <<>> THEN st ELSE
    [st EXCEPT !.hist=Prefix(@,Head(tail).index-1)\o tail]
EmptyReady == [active |-> FALSE, id |-> 0, hs |-> EmptyHS, hasHS |-> FALSE,
    ss |-> [role |-> "Follower",lead |-> 0], hasSS |-> FALSE,
    entries |-> <<>>, snapshot |-> EmptySnapshot, committed |-> <<>>, messages |-> EmptyBag,
    remainingMessages |-> EmptyBag,
    reads |-> <<>>, hist |-> <<>>, cursor |-> 0, fromApplied |-> 0, mustSync |-> FALSE,
    started |-> {}, done |-> {}, installed |-> {}, published |-> FALSE, queued |-> FALSE]
EmptyApp == [hist |-> <<>>, jobs |-> <<>>, reads |-> <<>>, config |-> EmptyConfig]
EmptyRequest == [status |-> "Unused", node |-> 0, kind |-> "Normal", target |-> 0,
    changes |-> <<>>, transition |-> "Legacy",
    weight |-> 0, encoded |-> 1, parent |-> 0, handoff |-> FALSE,
    core |-> "", result |-> "", context |-> 0, beforeWrites |-> {}, completed |-> FALSE]
EmptyHistory == [wins |-> {}, grants |-> {}, campaigns |-> {}, obligations |-> {},
    promises |-> {}, applied |-> {}, writes |-> {}, readResults |-> {},
    acks |-> {}, readyChecks |-> {}, recovery |-> {}, outcomes |-> {},
    commitUses |-> {}, snapshots |-> {}, autoLeaveChecks |-> {}, restoreChecks |-> {},
    liveOK |-> TRUE, sent |-> {}, lostReads |-> {}, events |-> {}]

(***************************************************************************
Integrated decision observers: S2/S3/S6. No protocol guard reads quality.
***************************************************************************)
EmptyQuality == [votes |-> {}, campaigns |-> {}, transfers |-> {}, effects |-> {}, proposals |-> {}]

NewResponses(r,a,types) ==
    {[type |-> m.type, term |-> m.term, to |-> m.to, reject |-> m.reject,
      count |-> a.out[m]-(IF m\in DOMAIN r.out THEN r.out[m] ELSE 0)]:
     m\in {x\in DOMAIN a.out:x.type\in types /\
            a.out[x]>(IF x\in DOMAIN r.out THEN r.out[x] ELSE 0)}}
VoteObservation(r,m,a) ==
    [node |-> r.id, learner |-> r.id\in r.config.learners,
     term |-> r.term, vote |-> r.vote, lead |-> r.lead,
     check |-> r.checkQuorum, elapsed |-> r.elapsed,
     lastIndex |-> Len(Hist(r)), lastTerm |-> IF Hist(r)= <<>> THEN 0 ELSE Hist(r)[Len(Hist(r))].term,
     message |-> m, afterTerm |-> a.term, afterVote |-> a.vote,
     responses |-> NewResponses(r,a,{"MsgVoteResp","MsgPreVoteResp"})]
\* raft.go:848-972; lease suppression precedes term reset. Learners and removed
\* nonlearners both use the ordinary vote/log checks; candidate membership is
\* deliberately not tested by the recipient.
VoteContract(o) ==
    LET m==o.message
        lease==m.term>o.term /\ ~m.forced /\ o.check /\ o.lead#0 /\ o.elapsed<ElectionTick
        stale==m.term#0 /\ m.term<o.term
        reset==~lease /\ ~stale /\ m.term>o.term /\ m.type="MsgVote"
        t==IF reset THEN m.term ELSE o.term
        v==IF reset THEN 0 ELSE o.vote
        lead==IF reset THEN 0 ELSE o.lead
        fresh==m.logTerm>o.lastTerm \/ (m.logTerm=o.lastTerm /\ m.index>=o.lastIndex)
        can==v=m.from \/ (v=0 /\ lead=0) \/ (m.type="MsgPreVote" /\ m.term>t)
        grant==~lease /\ ~stale /\ fresh /\ can
        silence==lease \/ (stale /\ m.type="MsgVote")
        expected==IF silence THEN {} ELSE
            {[type |-> IF m.type="MsgVote" THEN "MsgVoteResp" ELSE "MsgPreVoteResp",
              term |-> IF grant THEN m.term ELSE t, to |-> m.from, reject |-> ~grant, count |-> 1]}
    IN /\ o.responses=expected /\ o.afterTerm=t
       /\ o.afterVote=IF grant /\ m.type="MsgVote" THEN m.from ELSE v

CampaignRequests(r,a) ==
    {[from |-> m.from, to |-> m.to, type |-> m.type, term |-> m.term,
      index |-> m.index, logTerm |-> m.logTerm, forced |-> m.forced,
      count |-> a.out[m]-(IF m\in DOMAIN r.out THEN r.out[m] ELSE 0)]:
     m\in {x\in DOMAIN a.out:x.type\in {"MsgVote","MsgPreVote"} /\
            a.out[x]>(IF x\in DOMAIN r.out THEN r.out[x] ELSE 0)}}
CampaignObservation(r,a) ==
    [node |-> r.id, voters |-> VoterIDs(r.config), config |-> r.config,
     role |-> r.role, pre |-> r.preVote,
     term |-> r.term, applied |-> r.applied, commit |-> r.commit, first |-> First(r), hist |-> Hist(r),
     trigger |-> "Hup", elapsed |-> r.elapsed, timeout |-> r.timeout,
     voteRequests |-> CampaignRequests(r,a),
     afterRole |-> a.role, afterTerm |-> a.term, fatal |-> a.fatal]
\* raft.go:622-632,733-775,863-887. Observe ALL ticks before checking eligibility.
\* Repeated PreCandidate Hup may emit identical PreVotes without changing term
\* or role; message multiplicity, recipient, freshness and transfer flag matter.
CampaignContract(o) ==
    LET tick==o.trigger="Tick"
        due==~tick \/ (o.role#"Leader" /\ o.elapsed+1>=o.timeout)
        ignore==~due \/ o.role="Leader" \/ o.node\notin o.voters
        badSlice==~ignore /\ o.applied+1<o.first
        pending==\E k\in (o.applied+1)..o.commit:o.hist[k].kind\in ConfKinds
        blocked==ignore \/ pending \/ badSlice
        singleton==IsSingleton(o.config)
        expected==IF blocked \/ singleton THEN {} ELSE
            {[from |-> o.node,to |-> n,type |-> IF o.pre THEN "MsgPreVote" ELSE "MsgVote",
              term |-> o.term+1,index |-> Len(o.hist),
              logTerm |-> IF o.hist= <<>> THEN 0 ELSE o.hist[Len(o.hist)].term,
              forced |-> FALSE,count |-> 1]:n\in o.voters\{o.node}}
    IN /\ o.voteRequests=expected
       /\ IF tick /\ o.role="Leader" THEN o.afterTerm=o.term
          ELSE IF badSlice THEN o.fatal="Hup unapplied slice compacted"
          ELSE IF blocked THEN o.afterRole=o.role /\ o.afterTerm=o.term
          ELSE /\ o.fatal=""
               /\ o.afterRole=IF singleton THEN "Leader" ELSE IF o.pre THEN "PreCandidate" ELSE "Candidate"
               /\ o.afterTerm=o.term+(IF ~o.pre \/ singleton THEN 1 ELSE 0)

TransferObservation(r,target,a) ==
    [node |-> r.id, target |-> target, voters |-> VoterIDs(r.config), learners |-> r.config.learners,
     old |-> r.transfer, after |-> a.transfer, elapsed |-> a.elapsed,
     caughtUp |-> IF target\in DOMAIN r.prs THEN r.prs[target].match=Len(Hist(r)) ELSE FALSE,
     responses |-> NewResponses(r,a,{"MsgTimeoutNow"}), term |-> r.term]
\* raft.go:1028-1037,1151-1188. Unknown/learner/same target are ignored;
\* self aborts a different transfer; a lagging eligible target is still admitted.
TransferContract(o) ==
    LET ignore==o.target\notin o.voters\cup o.learners \/ o.target\in o.learners \/ o.target=o.old
        accept==~ignore /\ o.target#o.node
        expected==IF ignore THEN o.old ELSE IF o.target=o.node THEN 0 ELSE o.target
    IN /\ o.after=expected
       /\ (accept => o.elapsed=0)
       /\ o.responses=IF accept /\ o.caughtUp THEN
            {[type |-> "MsgTimeoutNow",term |-> o.term,to |-> o.target,reject |-> FALSE,count |-> 1]} ELSE {}

EffectObservation(r,e,a,qs) ==
    [node |-> r.id, entry |-> e, before |-> r.config, after |-> a.config,
     committed |-> Prefix(Hist(r),r.commit),
     request |-> IF e.id\in DOMAIN qs THEN qs[e.id] ELSE EmptyRequest]
\* README.md:120, node.go:135-138,159-163, raft.go:1417-1512.
\* Cancellation at invocation is not cancellation of a committed ConfChange.
\* Deterministic CancelChanges models the caller's zero-NodeID callback choice.
EffectContract(o) ==
    LET e==o.entry b==o.before q==o.request
    IN /\ o.after=ConfigAfter(b,e)
       /\ e.index\in DOMAIN o.committed /\ o.committed[e.index]=e
       /\ IF e.id=0 /\ e.kind="AddVoter" THEN
               e.term=1 /\ e.target\in SeqSet(BootPeers)
          ELSE IF e.id=0 THEN IsLeave(e)
          ELSE e.id\in RequestId /\ q.handoff /\ q.kind=e.kind /\
               IF e.kind="V2" THEN q.changes=e.changes /\ q.transition=e.transition
               ELSE q.target=e.target

ProposalObservation(r,es,a,qs) ==
    [node |-> r.id, role |-> r.role, voters |-> VoterIDs(r.config), learners |-> r.config.learners,
     lead |-> r.lead, noForward |-> r.noForward, transfer |-> r.transfer,
     quota |-> r.quota, pending |-> r.pendingConf, applied |-> r.applied,
     before |-> Hist(r), entries |-> es, after |-> Hist(a), decision |-> a.decision,
     requests |-> qs]
\* Independently specify the content relation (including rewritten no-op) and
\* admission in both directions. Source: raft.go:962-994,1236-1250; node.go:130-138.
ProposalContract(o) ==
    LET rewritten=={k\in DOMAIN o.entries:o.entries[k].kind\in ConfKinds /\
             (o.pending>o.applied \/ \E j\in 1..(k-1):o.entries[j].kind\in ConfKinds)}
        effective==[k\in DOMAIN o.entries |-> IF k\in rewritten THEN
            Entry(0,0,"Normal",0,0,0,EmptyEncoded) ELSE o.entries[k]]
        weight==Weight(effective)
        expected==IF o.role="Leader" THEN
            IF o.node\notin o.voters\cup o.learners THEN "DropRemoved"
            ELSE IF o.transfer#0 THEN "DropTransfer"
            ELSE IF o.quota>0 /\ o.quota+weight>MaxUncommitted THEN "DropQuota" ELSE "Accepted"
          ELSE IF o.role#"Follower" \/ o.lead=0 THEN "DropNoLeader"
          ELSE IF o.noForward THEN "DropForwardDisabled" ELSE "Forwarded"
    IN /\ o.decision=expected
       /\ IF expected="Accepted" THEN
            /\ Len(o.after)=Len(o.before)+Len(effective)
            /\ Prefix(o.after,Len(o.before))=o.before
            /\ \A k\in DOMAIN effective:
                 LET e==o.after[Len(o.before)+k] want==effective[k] IN
                 /\ e.kind=want.kind /\ e.id=want.id /\ e.target=want.target
                 /\ e.changes=want.changes /\ e.transition=want.transition
                 /\ (e.id#0 => e.id\in RequestId /\ o.requests[e.id].kind=e.kind /\
                      IF e.kind="V2" THEN o.requests[e.id].changes=e.changes
                      ELSE o.requests[e.id].target=e.target)
          ELSE o.after=o.before

\* Retain the last action's evidence only: no protocol pruning, no unbounded
\* accumulated observer history. The invariants check every observed transition.
QualityEvent(event,p) ==
    CASE event="Receive" ->
        LET m==p.message r==raft[m.to] a==raft'[m.to] IN
        [EmptyQuality EXCEPT
          !.votes=IF m.type\in {"MsgVote","MsgPreVote"} THEN {VoteObservation(r,m,a)} ELSE {},
          !.transfers=IF m.type="MsgTransferLeader" /\ r.role="Leader" /\ m.term\in {0,r.term}
                      THEN {TransferObservation(r,m.from,a)} ELSE {},
          !.proposals=IF m.type="MsgProp" /\ m.term\in {0,r.term}
                      THEN {ProposalObservation(r,m.entries,a,requests)} ELSE {}]
      [] event="Campaign" -> [EmptyQuality EXCEPT !.campaigns={CampaignObservation(raft[p.node],raft'[p.node])}]
      [] event="Tick" -> [EmptyQuality EXCEPT !.campaigns={
           [CampaignObservation(raft[p.node],raft'[p.node]) EXCEPT !.trigger="Tick"]}]
      [] event="TransferLeader" -> IF raft[p.node].role="Leader" THEN
            [EmptyQuality EXCEPT !.transfers={TransferObservation(raft[p.node],p.target,raft'[p.node])}] ELSE EmptyQuality
      [] event="Propose" ->
         LET q==requests[p.id] e==RequestEntry(q,p.id) IN
         [EmptyQuality EXCEPT !.proposals={ProposalObservation(raft[p.node],<<e>>,raft'[p.node],requests)}]
      [] event="ApplyEntry" ->
         LET e==Head(Head(application[p.node].jobs).entries) IN
         IF e.kind\in ConfKinds THEN [EmptyQuality EXCEPT
            !.effects={EffectObservation(raft[p.node],e,raft'[p.node],requests)}] ELSE EmptyQuality
      [] OTHER -> EmptyQuality
\* REQ-EVIDENCE VoteDecisionEligibility
\* intent:   Every vote or pre-vote request a node handles, learners included, is granted only as the voting rules allow (no grant or term change inside a leader lease, no term change for a pre-vote, term adoption on a newer MsgVote, at most one vote per term, candidate log at least as up-to-date), and a granted response carries the request's term.
\* status:   mixed
\* evidence: comment source/raft.go:833 "If a server receives a RequestVote request within the minimum election timeout" -> lease suppression: no term update and no grant inside the lease
\* evidence: test source/raft_paper_test.go:234 TestFollowerVote "each follower will vote for at most one" -> at most one vote per term, a repeat vote for the same candidate is granted
\* evidence: comment source/log.go:275 "If the logs have last entries with different terms, then the log with the" -> log freshness rule used for the grant
\* evidence: comment source/raft.go:953 "When responding to Msg{Pre,}Vote messages we include the term" -> a granted response carries the request's term
\* evidence: history abb533c27 (raft: let learners vote) "It turns out that that learners must be allowed to cast votes." -> learners included
\* evidence: doc source/doc.go:262 "no node increases its term" -> no term change for a pre-vote
\* evidence: doc source/doc.go:248 "If leader or candidate receives 'MsgVote' with higher term, it will revert" -> term adoption on a newer MsgVote
\* evidence: test source/raft_test.go:395 TestLearnerCanVote "expected learner to not reject vote" -> a learner answers a MsgVote with exactly one message (the reject check as written is vacuous for MsgVoteResp)
\* evidence: impl source/raft.go:925 "We can vote if this is a repeat of a vote we've already cast..."
\* evidence: impl source/raft.go:932 "if canVote && r.raftLog.isUpToDate(m.Index, m.LogTerm) {"
\* watch:    raft.go:Step (term handling, MsgVote/MsgPreVote); log.go:isUpToDate; raft.go:reset; raft.go:becomeFollower; raft.go:send
\* verified: V02
\* note:     VoteContract (base.tla) carries the content; not split because all clauses share the LET definitions of one contract. TestRejectStaleTermMessage (raft_paper_test.go:77) steps a stale MsgApp, not a vote, so it was removed: it does not assert anything about votes. doc.go:246-247 says a stale MsgVote "will be rejected ('MsgVoteResp' is returned with Reject true)", which contradicts the silence the formula expects for a stale MsgVote.
\* clause lease, pre-vote term and term-adoption rules: requirement — raft.go:833-834 (quotes Raft thesis), raft.go:842 "Never change our term in response to a PreVote", doc.go:248, doc.go:260-263
\* clause grant = can /\ fresh: requirement — raft_paper_test.go:234 TestFollowerVote, log.go:273-278, raft_paper_test.go:823 TestVoter
\* clause learners follow the same rules: requirement — abb533c27, raft.go:933-950
\* clause response term (m.term when granted): requirement — comment raft.go:953-961; local term on rejection: impl-abstraction — raft.go:889, raft.go:971
\* clause exact response multiset (one response; silence for lease and stale MsgVote; reject response for stale MsgPreVote): impl-abstraction — raft.go:837, raft.go:889-894; no test covers stale votes and doc.go:246-247 describes a reject response instead of silence
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   narrowed intent from "answered exactly" to the grant rules plus response term, retyped the narrating raft.go:925 comment to impl, removed the MsgApp-only stale test, added TestFollowerVote/log.go:275/doc.go:248 already named in the clause lines, and recorded the doc.go:247 contradiction.
VoteDecisionEligibility == \A o\in quality.votes:VoteContract(o)
\* REQ-EVIDENCE CampaignDecisionEligibility
\* intent:   Every Hup or election tick produces exactly the prescribed campaign: only a due, promotable voter with no pending unapplied configuration change campaigns; pre-vote keeps the term and a real campaign increments it; requests go to every other voter with the candidate's last index and term.
\* status:   mixed
\* evidence: history cd227fb83^:node.go:141 (removed by cd227fb83, raft: hide Campaign rules on applying all entries) "it MUST apply all pending configuration changes if there is any." -> a pending unapplied configuration change must be applied before campaigning (rule moved from the caller into raft)
\* evidence: test source/raft_test.go:3921 TestLearnerCampaign "a learner won't campaign even if it receives" -> only a promotable voter campaigns
\* evidence: test source/raft_paper_test.go:772 TestVoteRequest "the vote request includes information about the candidate" -> exactly one request to every other voter, with term+1 and the candidate's last index and term
\* evidence: doc source/doc.go:262 "no node increases its term" -> pre-vote keeps the term
\* evidence: doc source/doc.go:209 "candidate has not received any heartbeat before the election timeout, it" -> a due (timed-out) non-leader campaigns on tick
\* evidence: impl source/raft.go:909 "if n := numOfPendingConf(ents); n != 0 && r.raftLog.committed > r.raftLog.applied {"
\* watch:    raft.go:Step (MsgHup); raft.go:tickElection; raft.go:campaign; raft.go:numOfPendingConf; raft.go:promotable; raft.go:becomePreCandidate; raft.go:becomeCandidate
\* verified: V02
\* note:     CampaignContract counts pending EntryConfChangeV2 entries (ConfKinds) as blocking, but raft.go:numOfPendingConf (and base.tla StepHup) count only EntryConfChange; a violation would point at that gap (out/concerns.md). Not split: one LET contract. The cd227fb83 quote is a removed comment line, not the commit message.
\* clause due/ignore (non-leader, voter, timeout reached on tick): requirement — raft_test.go:3921 TestLearnerCampaign, raft_test.go:311 TestLearnerElectionTimeout, doc.go:207-211
\* clause pending configuration change blocks the campaign: requirement — cd227fb83 replaced a caller MUST-rule with this internal check; raft.go:909-911
\* clause badSlice => fatal "Hup unapplied slice compacted": impl-abstraction — raft.go:905-907 Panicf only
\* clause vote requests, resulting role and term: requirement — raft_paper_test.go:772-774 TestVoteRequest, doc.go:260-263, raft.go:778-787
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   kept intent and status; corrected the cd227fb83 location (the quote is a removed node.go line, not the message) and added doc.go:209 which the clause line already relied on.
CampaignDecisionEligibility == \A o\in quality.campaigns:CampaignContract(o)
\* REQ-EVIDENCE TransferDecisionEligibility
\* intent:   Every leader-transfer request is handled as prescribed: unknown, learner, or already-pending targets are ignored; a self target aborts any pending transfer; another voter becomes the transferee with the election timer reset; MsgTimeoutNow is sent on acceptance only to a caught-up target.
\* status:   mixed
\* evidence: comment source/raft.go:279 "Follow the procedure defined in raft thesis 3.10." -> the transfer follows the thesis procedure (target caught up before MsgTimeoutNow)
\* evidence: comment source/raft.go:1227 "Transfer leadership should be finished in one electionTimeout, so reset r.electionElapsed." -> election timer reset on acceptance
\* evidence: test source/raft_test.go:3646 TestLeaderTransferSecondTransferToSameNode "to the same node should not extend the timeout while the first one is pending." -> an already-pending target is ignored
\* evidence: test source/raft_test.go:3509 TestLeaderTransferToNonExistingNode "Transfer leadership to non-existing node, there will be noop." -> unknown target ignored
\* evidence: test source/raft_test.go:3499 TestLeaderTransferToSelf "Transfer leadership to self, there will be noop." -> self target leaves no transfer pending
\* evidence: test source/raft_test.go:3604 TestLeaderTransferBack "verifies leadership can transfer back to self when last transfer is pending." -> a self target aborts a pending transfer
\* evidence: test source/raft_test.go:3624 TestLeaderTransferSecondTransferToAnotherNode "verifies leader can transfer to another node" -> another voter replaces a pending transferee
\* evidence: history db54973bb (raft: prevent learners from becoming leader) "The newly added test also verifies that leadership transfers to" -> learner target ignored (message continues "learners are ignored")
\* evidence: impl source/raft.go:1230 "if pr.Match == r.raftLog.lastIndex() {"
\* watch:    raft.go:stepLeader (MsgTransferLeader); raft.go:sendTimeoutNow; raft.go:abortLeaderTransfer; raft.go:stepFollower (MsgTransferLeader); raft.go:stepLeader (MsgAppResp transfer branch)
\* verified: V02
\* note:     TransferContract carries the content; not split (one LET contract). The db54973bb quote continues "learners are ignored" on the next message line.
\* clause ignore unknown or same target, self aborts, other voter replaces: requirement — raft_test.go:3499, 3509, 3604, 3624, 3646
\* clause learner target ignored: requirement — db54973bb message; raft_test.go:3944 "TransferLeader already checks that the recipient is not a learner"
\* clause election timer reset on acceptance: requirement — raft.go:1227
\* clause MsgTimeoutNow only to a caught-up target: requirement — raft.go:279 (thesis 3.10)
\* clause MsgTimeoutNow sent at once whenever the target is already caught up: impl-abstraction — raft.go:1230-1235 only; raft_test.go:3360 and 3448 assert eventual transfer, not the immediate send
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   narrowed the MsgTimeoutNow part to "only to a caught-up target" (the immediate send is impl only; the cited tests assert eventual transfer), added TestLeaderTransferBack/SecondTransferToAnotherNode for the abort and replace cases, and corrected the clause that cited the unrelated raft.go:1083 comment.
TransferDecisionEligibility == \A o\in quality.transfers:TransferContract(o)
\* REQ-EVIDENCE RequestCorrelatedConfigurationEffects
\* intent:   Applying a committed configuration entry changes the node's configuration exactly as that change prescribes, or not at all if the caller cancelled it, and every applied configuration entry is committed.
\* status:   mixed
\* evidence: doc source/README.md:178 "After config change is committed, some committed entry with type raftpb.EntryConfChange" -> every applied configuration entry is committed
\* evidence: doc source/README.md:120 "The configuration change may be cancelled at this point by setting the NodeID" -> not at all if the caller cancelled it
\* evidence: comment source/confchange/confchange.go:158 "etcd replaces the NodeID with zero if it decides (downstream of" -> a zeroed (cancelled) change is ignored
\* evidence: test source/rawnode_test.go:108 TestRawNodeProposeAndConfChange "tests the configuration change mechanism. Each" -> the resulting configuration matches the change (for the tested simple and joint changes)
\* evidence: impl source/raft.go:1469 "if cc.LeaveJoint() {"
\* watch:    raft.go:applyConfChange; confchange/confchange.go:Simple; confchange/confchange.go:EnterJoint; confchange/confchange.go:LeaveJoint; confchange/confchange.go:apply; raftpb/confchange.go:EnterJoint; raftpb/confchange.go:LeaveJoint; raft.go:advance (auto-leave)
\* verified: V02
\* note:     EffectContract carries the content; not split (one LET contract).
\* clause after = ConfigAfter(before,e) for valid changes: requirement — README.md:178, confchange/confchange.go:36-150 contracts, confchange/testdata/*.txt
\* clause invalid change leaves the configuration unchanged: impl-abstraction — the library panics (raft.go:1477-1479 "TODO(tbg): return the error to the caller") and the model's ConfigAfter keeps cfg
\* clause entry is committed: requirement — README.md:178
\* clause origin is bootstrap, auto-leave, or a matching handed-off request: model-internal — request ids are model ghosts; bootstrap entries per bootstrap.go:51-60
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, model-internal, requirement); handle clause by clause
\* review:   narrowed the intent by removing the model-internal origin clause and the invalid-change case (no non-impl evidence), both now recorded as clause lines.
RequestCorrelatedConfigurationEffects == \A o\in quality.effects:EffectContract(o)
\* REQ-EVIDENCE ProposalConfigurationDecisions
\* intent:   An accepted proposal extends the log by exactly the proposed entries in order, with a configuration entry replaced by an empty normal entry while another configuration change is pending or earlier in the same batch; a proposal dropped for a pending transfer, quota overflow, candidacy or disabled forwarding leaves the log unchanged.
\* status:   mixed
\* evidence: doc source/README.md:195 "any proposed membership change is simply disallowed while any uncommitted change appears" -> configuration entry rewritten while another change is pending
\* evidence: comment source/raft.go:281 "Only one conf change may be pending (in the log, but not yet" -> rewritten while pending or earlier in the same batch
\* evidence: test source/raft_test.go:3043 TestStepIgnoreConfig "EntryConfChange type when the first one is uncommitted, the node will set" -> the second configuration proposal becomes an empty normal entry
\* evidence: comment source/node.go:137 "returned. In particular, configuration changes are dropped unless the" -> configuration changes are not applied while a prior one is unapplied
\* evidence: test source/raft_paper_test.go:390 TestLeaderStartReplication "the leader appends the proposal to its log as a new entry" -> accepted entries are appended at the end of the log
\* evidence: impl source/raft.go:1034 "m.Entries[i] = pb.Entry{Type: pb.EntryNormal}"
\* watch:    raft.go:stepLeader (MsgProp); raft.go:appendEntry; raft.go:increaseUncommittedSize; raft.go:stepFollower (MsgProp); raft.go:stepCandidate (MsgProp); node.go:run (propc)
\* verified: V02
\* note:     ProposalContract carries the content; not split (one LET contract).
\* clause decision table: requirement for the transfer, quota, candidate and forwarding drops (evidence as in OutcomeSoundness); follower-without-leader drop: impl-abstraction; removed-leader drop: unknown (only the narrating comment raft.go:1018); precedence order and default acceptance: impl-abstraction
\* clause configuration rewrite to empty entry: requirement — README.md:195, raft.go:281-286, raft_test.go:3045 TestStepIgnoreConfig
\* clause accepted entries appended in order, others leave log unchanged: requirement — raft_paper_test.go:389-390 TestLeaderStartReplication
\* clause entry ids match handed-off requests: model-internal — request ids are model ghosts
\* relabel:  requirement -> mixed (clause statuses: model-internal, requirement); handle clause by clause
\* review:   narrowed the intent to the content and drop rules that have non-impl evidence; the exact decision table (precedence, removed-leader drop) and ghost ids stay in clause lines.
ProposalConfigurationDecisions == \A o\in quality.proposals:ProposalContract(o)

\* node.go:213-249, rawnode.go:40-58, bootstrap.go:29-76. NewRawNode is
\* term-zero and explicit Bootstrap creates term-one configuration entries.
InitialRaft(n,timeout) ==
    LET joining==n\in Joining
        h==IF joining THEN <<>> ELSE BootLog
        cfg==IF joining THEN EmptyConfig ELSE BootConfig
    IN [id |-> n, alive |-> TRUE, incarnation |-> 0,
        term |-> IF joining THEN 0 ELSE 1, vote |-> 0,
        role |-> "Follower", lead |-> 0, config |-> cfg, cfgHist |-> h,
        store |-> Store(<<>>,EmptySnapshot,0,EmptyHS), unstable |-> h, uoff |-> 1,
        usnap |-> EmptySnapshot, commit |-> Len(h), applied |-> 0,
        prs |-> [p \in cfg.voters |-> Progress(0,Len(h)+1,TRUE)],
        yes |-> {}, no |-> {}, pendingConf |-> 0, quota |-> 0,
        elapsed |-> 0, heartbeat |-> 0, timeout |-> timeout, transfer |-> 0,
        preVote |-> n\in PreVoteNodes, checkQuorum |-> n\in CheckQuorumNodes,
        noForward |-> n\in NoForwardNodes, out |-> EmptyBag, readQueue |-> <<>>,
        readStates |-> <<>>, snapAvailable |-> TRUE, fatal |-> "",
        prevHS |-> EmptyHS, prevSS |-> [role |-> "Follower",lead |-> 0],
        readySeq |-> 0, nodeLead |-> 0, propcEnabled |-> FALSE, decision |-> "", wins |-> {}, grants |-> {}, campaigns |-> {},
        commitUses |-> {}]
InitialTimeoutAssignments == [Server -> ElectionTick..(2*ElectionTick-1)]
ProtocolInit ==
        /\ \E timeouts \in InitialTimeoutAssignments:
              raft=[n \in Server |-> InitialRaft(n,timeouts[n])]
        /\ disk=[n \in Server |-> EmptyDisk]
        /\ ready=[n \in Server |-> EmptyReady]
        /\ application=[n \in Server |-> EmptyApp]
        /\ requests=[id \in RequestId |-> EmptyRequest]
        /\ wire=EmptyBag /\ history=EmptyHistory

Init == ProtocolInit /\ quality=EmptyQuality

\* Ghost observer: record durable quorums whether or not downstream properties hold.
DurableObligations(rs,ds) ==
    {[term |-> rs[n].term, hist |-> Prefix(Hist(rs[n]),rs[n].commit)] :
     n \in {j \in Server:rs[j].alive /\ rs[j].role="Leader" /\ rs[j].commit>0 /\
         Term(rs[j],rs[j].commit)=rs[j].term /\ rs[j].config.voters#{} /\
         JointWon(rs[j].config,{p \in VoterIDs(rs[j].config):
                    DiskHas(ds[p],Prefix(Hist(rs[j]),rs[j].commit))})}}
Observe(h,rs,ds,event) == [h EXCEPT
    !.wins=@\cup UNION {rs[n].wins:n\in Server},
    !.grants=@\cup UNION {rs[n].grants:n\in Server},
    !.campaigns=@\cup UNION {rs[n].campaigns:n\in Server},
    !.commitUses=@\cup UNION {rs[n].commitUses:n\in Server},
    !.obligations=@\cup DurableObligations(rs,ds), !.events=@\cup {event}]
\* node.go:339-351: proposal channel re-enables on a later leader change, even
\* after a removal callback disabled it. This wrapper-local state is observable.
WrapperLoop(r) == IF r.id\in RawNodes THEN r ELSE
    [r EXCEPT !.propcEnabled=IF r.nodeLead#r.lead THEN r.lead#0 ELSE @, !.nodeLead=r.lead]
Live(n) == raft[n].alive /\ raft[n].fatal=""
\* CommittedHistory records overwritten commitments within a live incarnation.
SetCore(n,a,event) ==
    /\ raft'=[raft EXCEPT ![n]=WrapperLoop(a)]
    /\ history'=Observe([history EXCEPT !.liveOK=@ /\
                     Covers(Hist(a),Prefix(Hist(raft[n]),raft[n].commit))],raft',disk,event)
CoreCall(n,a,event) == /\ Live(n) /\ SetCore(n,a,event)
    /\ UNCHANGED <<disk,ready,application,requests,wire>>
ProtocolTick(n,timeout) ==
                   CoreCall(n,TickCore(raft[n],timeout),"Tick")
ProtocolCampaign(n,timeout) ==
                       CoreCall(n,StepHup(raft[n],timeout),"Campaign")
\* rawnode.go:124-134: quiescing requires equal histories and no pending traffic.
ProtocolTickQuiesced(n) ==
                   /\ n\in RawNodes /\ wire=EmptyBag
    /\ \A p\in Server: raft[p].out=EmptyBag /\ Hist(raft[p])=Hist(raft[n])
    /\ CoreCall(n,[raft[n] EXCEPT !.elapsed=@+1],"TickQuiesced")
ProtocolTransferLeader(n,target,timeout) ==
                                    CoreCall(n,
    Step(raft[n],Message("MsgTransferLeader",target,n,0),timeout),"TransferLeader")

\* node.go:473-509, rawnode.go:143-164. Invocation is not logging or success.
ProtocolInvoke(n,id,kind,target,w,z,parent,ctx) ==
    /\ requests[id].status="Unused"
    /\ kind\in Kinds\cup {"Read"}
    /\ (kind="Read" => \A j\in RequestId:
           requests[j].status#"Unused" /\ requests[j].kind="Read" => requests[j].context#ctx)
    /\ (kind\in {"AddVoter","AddLearner"} =>
           ~\E h\in history.applied:\E k\in DOMAIN h:
               h[k].kind="Remove" /\ h[k].target=target /\ h[k].id\notin CancelChanges /\
               target\in ConfigOf(Prefix(h,k-1)).voters\cup ConfigOf(Prefix(h,k-1)).learners)
    /\ parent=0 \/ (parent\in RequestId /\ requests[parent].status#"Unused")
    /\ requests'=[requests EXCEPT ![id]=[EmptyRequest EXCEPT !.status="Invoked",
        !.node=n, !.kind=kind, !.target=target, !.weight=w, !.encoded=z,
        !.changes=IF kind\in LegacyConfKinds THEN <<Change(kind,target)>> ELSE <<>>,
        !.parent=parent, !.context=ctx, !.beforeWrites=history.writes]]
    /\ UNCHANGED <<raft,disk,ready,application,wire,history>>
\* node.go:428-442, rawnode.go:94-102; V2 marshaling is distinct but handoff is
\* the same proposal path. Changes are one atomic ConfChangeV2 payload.
ProtocolInvokeV2(n,id,changes,transition,w,z,parent) ==
    /\ requests[id].status="Unused"
    /\ parent=0 \/ (parent\in RequestId /\ requests[parent].status#"Unused")
    /\ transition\in {"Auto","JointImplicit","JointExplicit"}
    /\ \A ch\in SeqSet(changes):ch.kind\in LegacyConfKinds /\ ch.target\in Server\cup{0}
    /\ requests'=[requests EXCEPT ![id]=[EmptyRequest EXCEPT !.status="Invoked",
        !.node=n, !.kind="V2", !.changes=changes, !.transition=transition,
        !.weight=w, !.encoded=z, !.parent=parent, !.context=id,
        !.beforeWrites=history.writes]]
    /\ UNCHANGED <<raft,disk,ready,application,wire,history>>
\* Handoff and core work are one serialized Node select/RawNode call; result is later.
ProtocolPropose(n,id,timeout) ==
    /\ Live(n) /\ requests[id].status="Invoked" /\ requests[id].node=n
    /\ requests[id].kind\in Kinds\cup {"V2"}
    /\ n\in RawNodes \/ raft[n].propcEnabled
    /\ LET q==requests[id]
           m==[Message("MsgProp",n,n,0) EXCEPT !.request=id,
                 !.entries= <<RequestEntry(q,id)>>]
           a==Step([raft[n] EXCEPT !.decision=""],m,timeout)
           result==IF n\notin RawNodes /\ q.kind\in ConfKinds THEN "Handoff"
                   ELSE a.decision
           outcome==[kind |-> q.kind, decision |-> a.decision, role |-> raft[n].role,
             member |-> n\in Members(raft[n]), lead |-> raft[n].lead,
             forwarding |-> ~raft[n].noForward, transfer |-> raft[n].transfer,
             quota |-> raft[n].quota, weight |->
                 Weight(RewriteConf(raft[n],m.entries,1).entries)]
       IN /\ raft'=[raft EXCEPT ![n]=WrapperLoop(a)]
          /\ requests'=[requests EXCEPT ![id].status="HandedOff", ![id].handoff=TRUE,
                        ![id].core=a.decision, ![id].result=result]
          /\ history'=Observe([history EXCEPT !.outcomes=@\cup {outcome}],raft',disk,"Propose")
    /\ UNCHANGED <<disk,ready,application,wire>>
ProtocolReadIndex(n,id,timeout) ==
    /\ Live(n) /\ requests[id].status="Invoked" /\ requests[id].kind="Read"
    /\ requests[id].node=n
    /\ LET m==[Message("MsgReadIndex",n,n,0) EXCEPT
                 !.context=requests[id].context, !.request=id]
       IN SetCore(n,Step(raft[n],m,timeout),"ReadIndex")
    /\ requests'=[requests EXCEPT ![id].status="HandedOff", ![id].handoff=TRUE,
                  ![id].result="Handoff"]
    /\ UNCHANGED <<disk,ready,application,wire>>
ProtocolReturnAPI(id) ==
                 /\ requests[id].status="HandedOff"
    /\ requests'=[requests EXCEPT ![id].status="Returned"]
    /\ UNCHANGED <<raft,disk,ready,application,wire,history>>
ProtocolCancel(id) ==
              /\ requests[id].status\in {"Invoked","HandedOff"}
    /\ requests'=[requests EXCEPT ![id].status="Canceled", ![id].result="Canceled"]
    /\ UNCHANGED <<raft,disk,ready,application,wire,history>>

\* node.go:366-370 / rawnode.go:174-182; wire contains only published valid messages.
ResponseTypes == {"MsgAppResp","MsgVoteResp","MsgPreVoteResp","MsgHeartbeatResp","MsgUnreachable"}
ProtocolReceive(m,timeout) ==
    /\ m\in DOMAIN wire /\ wire[m]>0 /\ Live(m.to)
    /\ LET r==raft[m.to]
           a==IF m.type\in ResponseTypes /\ m.from\notin Members(r) THEN r
              ELSE Step(r,m,timeout)
           restoreCheck==[fresh |-> m.snapshot.index>r.commit,
             follower |-> r.role="Follower",
             sourceMember |-> r.id\in m.snapshot.config.voters\cup m.snapshot.config.learners,
             fullMember |-> r.id\in VoterIDs(m.snapshot.config)\cup m.snapshot.config.learners,
             matches |-> Matches(r,m.snapshot.index,m.snapshot.term),
             snapshotIndex |-> m.snapshot.index, snapshotConfig |-> m.snapshot.config,
             afterCommit |-> a.commit, afterConfig |-> a.config]
           h==IF m.type="MsgSnap" THEN
                [history EXCEPT !.restoreChecks=@\cup {restoreCheck}] ELSE history
       IN /\ raft'=[raft EXCEPT ![m.to]=WrapperLoop(a)]
          /\ history'=Observe([h EXCEPT !.liveOK=@ /\
                 Covers(Hist(a),Prefix(Hist(r),r.commit))],raft',disk,"Receive")
    /\ wire'=RemoveBag(wire,m)
    /\ UNCHANGED <<disk,ready,application,requests>>
ProtocolLose(m) ==
           /\ m\in DOMAIN wire /\ wire[m]>0
    /\ wire'=RemoveBag(wire,m)
    /\ UNCHANGED <<raft,disk,ready,application,requests,history>>
ProtocolDuplicate(m) ==
                /\ m\in DOMAIN wire /\ wire[m]>0
    /\ wire'=AddBag(wire,m)
    /\ UNCHANGED <<raft,disk,ready,application,requests,history>>
\* Public reporting after an actual published message, including delayed status.
ProtocolReportSnapshot(n,m,failed,timeout) ==
    /\ m\in history.sent /\ m.type="MsgSnap" /\ m.from=n
    /\ CoreCall(n,Step(raft[n],[Message("MsgSnapStatus",m.to,n,0) EXCEPT !.reject=failed],timeout),"ReportSnapshot")
ProtocolReportUnreachable(n,m,timeout) ==
    /\ m\in history.sent /\ m.from=n
    /\ CoreCall(n,Step(raft[n],Message("MsgUnreachable",m.to,n,0),timeout),"ReportUnreachable")

\* node.go:553-584 / log.go:151-160: clamped, encoded-size-limited Ready page.
NewReady(r) ==
    LET es==LimitSize(SubSeq(Hist(r),Max(r.applied+1,First(r)),r.commit),MaxReadySize)
        cursor==IF es# <<>> THEN es[Len(es)].index ELSE r.usnap.index
    IN [EmptyReady EXCEPT !.active=TRUE, !.id=r.readySeq+1,
        !.hs=HS(r), !.hasHS=HS(r)#r.prevHS, !.ss=SS(r), !.hasSS=SS(r)#r.prevSS,
        !.entries=r.unstable, !.snapshot=r.usnap, !.committed=es, !.messages=r.out, !.remainingMessages=r.out,
        !.reads=r.readStates, !.hist=Hist(r), !.cursor=cursor, !.fromApplied=r.applied,
        !.mustSync=r.unstable# <<>> \/ r.term#r.prevHS.term \/ r.vote#r.prevHS.vote]
ContainsUpdates(b) == b.hasHS \/ b.hasSS \/ b.entries# <<>> \/ b.snapshot.index>0 \/
                      b.committed# <<>> \/ b.messages#EmptyBag \/ b.reads# <<>>
ProtocolReady(n) ==
    /\ Live(n) /\ ~ready[n].active
    /\ LET r==raft[n] b==NewReady(r) IN
       /\ (ContainsUpdates(b) \/ n\in RawNodes)
       /\ ready'=[ready EXCEPT ![n]=b]
       \* rawnode.go:119-146 accepts public RawNode.Ready immediately;
       \* node.go:306-320,385-387 accepts only after channel delivery.
       \* UPDATE-MAP
       \* code: rawnode.go:Ready,acceptReady; node.go:run Ready delivery
       \* update: Update!AffectedReadyActions
       /\ raft'=[raft EXCEPT ![n]=[r EXCEPT
            !.out=EmptyBag,
            !.readySeq=b.id,
            !.readStates= <<>>,
            !.prevSS=b.ss]]
       /\ application'=[application EXCEPT ![n].reads=@\o b.reads]
       /\ history'=Observe([history EXCEPT !.readyChecks=@\cup
              {[from |-> r.applied, first |-> First(r), cursor |-> b.cursor,
                entries |-> b.committed, snapshot |-> b.snapshot.index,
                commit |-> r.commit, raw |-> n\in RawNodes,
                outBefore |-> r.out, outAfter |-> raft'[n].out,
                readsBefore |-> r.readStates, readsAfter |-> raft'[n].readStates,
                quotaBefore |-> r.quota, quotaAfter |-> raft'[n].quota]}],raft',disk,"Ready")
    /\ UNCHANGED <<disk,requests,wire>>
Parts(b) == {"Entries","HS","Snapshot"}
Needs(b,part) == CASE part="Entries" -> b.entries# <<>>
                   [] part="HS" -> b.hasHS
                   [] OTHER -> b.snapshot.index>0
Done(b,part) == ~Needs(b,part) \/ part\in b.done
Persisted(b) == \A part\in Parts(b):Done(b,part)
\* README.md:116: named adapter variants, no independent half-HardState writes.
ProtocolStartPersist(n,part) ==
    /\ Live(n) /\ ready[n].active /\ part\notin ready[n].started
    /\ part\in IF PersistPolicy="Atomic" THEN {"All"} ELSE Parts(ready[n])
    /\ PersistPolicy#"EntriesHSnap" \/ part="Entries" \/
         (Done(ready[n],"Entries") /\ (part="HS" \/ Done(ready[n],"HS")))
    /\ ready'=[ready EXCEPT ![n].started=@\cup {part}]
    /\ UNCHANGED <<raft,disk,application,requests,wire,history>>
PersistPart(d,b,part) ==
    CASE part="Entries" -> DiskAppend(d,b.entries)
      [] part="HS" -> IF b.hasHS THEN [d EXCEPT !.hs=b.hs] ELSE d
      [] part="Snapshot" -> IF b.snapshot.index>0 THEN [d EXCEPT !.snapshot=b.snapshot] ELSE d
      [] OTHER -> LET a==DiskAppend(d,b.entries)
                      c==IF b.hasHS THEN [a EXCEPT !.hs=b.hs] ELSE a
                  IN IF b.snapshot.index>0 THEN [c EXCEPT !.snapshot=b.snapshot] ELSE c
ProtocolCompletePersist(n,part) ==
    /\ Live(n) /\ ready[n].active /\ part\in ready[n].started /\ part\notin ready[n].done
    /\ disk'=[disk EXCEPT ![n]=PersistPart(@,ready[n],part)]
    /\ ready'=[ready EXCEPT ![n].done=@\cup IF part="All" THEN Parts(ready[n])\cup {"All"} ELSE {part}]
    /\ history'=Observe(history,raft,disk',"CompletePersist")
    /\ UNCHANGED <<raft,application,requests,wire>>
\* storage.go:172-185,239-269: separate visibility calls following completed writes.
ProtocolStorageApplySnapshot(n) ==
    /\ Live(n) /\ ready[n].active /\ Done(ready[n],"Snapshot")
    /\ "Snapshot"\notin ready[n].installed
    /\ LET b==ready[n] r==raft[n]
           a==IF b.snapshot.index=0 \/ b.snapshot.index<=r.store.snapshot.index THEN r ELSE
                 [r EXCEPT !.store=Store(b.snapshot.hist,b.snapshot,b.snapshot.index,r.store.hs)]
       IN SetCore(n,a,"StorageApplySnapshot")
    /\ ready'=[ready EXCEPT ![n].installed=@\cup {"Snapshot"}]
    /\ UNCHANGED <<disk,application,requests,wire>>
ProtocolStorageAppend(n) ==
    /\ Live(n) /\ ready[n].active /\ Done(ready[n],"Entries")
    /\ "Snapshot"\in ready[n].installed /\ "Entries"\notin ready[n].installed
    /\ LET b==ready[n] r==raft[n]
           tail==SelectSeq(b.entries,LAMBDA e:e.index>r.store.cut)
           a==IF tail# <<>> /\ Head(tail).index>Len(r.store.hist)+1
              THEN Fatal(r,"Storage.Append gap")
              ELSE [r EXCEPT !.store=StoreAppend(@,b.entries)]
       IN SetCore(n,a,"StorageAppend")
    /\ ready'=[ready EXCEPT ![n].installed=@\cup {"Entries"}]
    /\ UNCHANGED <<disk,application,requests,wire>>
ProtocolStorageSetHardState(n) ==
    /\ Live(n) /\ ready[n].active /\ Done(ready[n],"HS")
    /\ "HS"\notin ready[n].installed
    /\ SetCore(n,IF ready[n].hasHS THEN [raft[n] EXCEPT !.store.hs=ready[n].hs] ELSE raft[n],"StorageSetHardState")
    /\ ready'=[ready EXCEPT ![n].installed=@\cup {"HS"}]
    /\ UNCHANGED <<disk,application,requests,wire>>

\* S1 published promises enter history even when their backing is invalid.
PromiseOK(n,m) ==
    /\ m.term=0 \/ disk[n].hs.term>=m.term \/ m.type\in {"MsgPreVote","MsgPreVoteResp"}
    /\ (m.type="MsgVoteResp" /\ ~m.reject) =>
          (disk[n].hs.term>m.term \/ (disk[n].hs.term=m.term /\ disk[n].hs.vote=m.to))
    /\ (m.type="MsgAppResp" /\ ~m.reject /\ m.index>0) =>
          (Len(m.witness)>=m.index /\ DiskHas(disk[n],Prefix(m.witness,m.index)))
    /\ m.commit>0 => DiskHas(disk[n],Prefix(m.witness,m.commit))
ProtocolPublish(n) ==
    /\ Live(n) /\ ready[n].active /\ ~ready[n].published
    /\ Done(ready[n],"HS")
    /\ SendPolicy="SameBatch" \/ (Done(ready[n],"Entries") /\ Done(ready[n],"Snapshot"))
    /\ IF ready[n].remainingMessages=EmptyBag THEN
          /\ ready'=[ready EXCEPT ![n].published=TRUE]
          /\ history'=Observe(history,raft,disk,"Publish")
          /\ UNCHANGED wire
       ELSE \E m\in DOMAIN ready[n].remainingMessages:
          /\ wire'=AddBag(wire,m)
          /\ ready'=[ready EXCEPT ![n].remainingMessages=RemoveBag(@,m),
                   ![n].published=BagCardinality(ready[n].remainingMessages)=1]
          /\ history'=Observe([history EXCEPT
             !.promises=@\cup {[message |-> m,backed |-> PromiseOK(n,m)]},
             !.obligations=IF m.commit>0 THEN
                 @\cup {[term |-> m.term,hist |-> Prefix(m.witness,m.commit)]} ELSE @,
             !.sent=@\cup {m}],raft,disk,"Publish")
    /\ UNCHANGED <<raft,disk,application,requests>>
\* node.go:145-157, README.md:120-122: queue stays ordered after early Advance.
ProtocolQueueApplication(n) ==
    /\ Live(n) /\ ready[n].active /\ Persisted(ready[n]) /\ ~ready[n].queued
    /\ LET b==ready[n] IN application'=[application EXCEPT ![n].jobs=
          IF b.snapshot.index=0 /\ b.committed= <<>> THEN @ ELSE
             Append(@,[batch |-> b.id, snapshot |-> b.snapshot, entries |-> b.committed])]
    /\ ready'=[ready EXCEPT ![n].queued=TRUE]
    /\ UNCHANGED <<raft,disk,requests,wire,history>>
\* rawnode.go:170-177, raft.go:556-587 and log_unstable.go:77-114.
\* Both wrappers accepted messages/read states before Advance. Advance preserves
\* any output produced after that acceptance and appends auto-leave after apply.
\* UPDATE-MAP
\* code: rawnode.go:Advance; raft.go:advance
\* update: Update!AffectedReadyActions
AdvanceCore(r,b,n) ==
    LET a==AppliedTo(r,b.cursor)
        leave==V2Entry(0,0,0,<<>>,"Auto",AutoLeaveWeight,AutoLeaveEncoded)
        auto==a.fatal="" /\ b.cursor>0 /\ a.config.autoLeave /\ b.cursor>=a.pendingConf /\ a.role="Leader"
        b0==IF auto THEN AppendEntry(a,<<leave>>) ELSE a
        b1==IF auto /\ AppendQuotaExceeded(a,<<leave>>) THEN [b0 EXCEPT !.pendingConf=Last(b0)] ELSE b0
        last==IF b.entries= <<>> THEN MissingEntry(0) ELSE b.entries[Len(b.entries)]
        stable==b.entries# <<>> /\ last.index>=b1.uoff /\ last.index<=Last(b1) /\
                 Term(b1,last.index)=last.term
    IN [b1 EXCEPT
        !.quota=Max(0,@-Weight(b.committed)),
        !.unstable=IF stable THEN Suffix(@,last.index+2-r.uoff) ELSE @,
        !.uoff=IF stable THEN last.index+1 ELSE @,
        !.usnap=IF b.snapshot.index>0 /\ r.usnap.index=b.snapshot.index THEN EmptySnapshot ELSE @,
        !.prevHS=b.hs]
ProtocolAdvance(n) ==
    /\ Live(n) /\ ready[n].active /\ Persisted(ready[n])
    /\ ready[n].installed=Parts(ready[n]) /\ ready[n].published /\ ready[n].queued
    /\ EarlyAdvance \/ application[n].jobs= <<>>
    /\ LET r==raft[n] b==ready[n] a==AdvanceCore(r,b,n) IN
       /\ raft'=[raft EXCEPT ![n]=a]
       /\ history'=Observe([history EXCEPT !.acks=@\cup
            {[before |-> Hist(r), after |-> Hist(a), oldSnap |-> r.usnap.index,
              batchSnap |-> b.snapshot.index, afterSnap |-> a.usnap.index,
              cursor |-> b.cursor, applied |-> a.applied,
              outBefore |-> r.out, outAfter |-> a.out,
              readsBefore |-> r.readStates, readsAfter |-> a.readStates,
              ssBefore |-> r.prevSS, ssAfter |-> a.prevSS]},
            !.autoLeaveChecks=@\cup
            {[eligible |-> r.config.autoLeave /\ b.cursor>=r.pendingConf /\ r.role="Leader",
              beforeLast |-> Last(r), afterHist |-> Hist(a), pending |-> a.pendingConf,
              decision |-> a.decision]}],raft',disk,"Advance")
    /\ ready'=[ready EXCEPT ![n]=EmptyReady]
    /\ UNCHANGED <<disk,application,requests,wire>>
\* Caller snapshot application completes separately from restore/persistence/Advance.
ProtocolApplySnapshot(n) ==
    /\ Live(n) /\ application[n].jobs# <<>>
    /\ Head(application[n].jobs).snapshot.index>0
    /\ LET j==Head(application[n].jobs) s==j.snapshot
           h==IF s.index>Len(application[n].hist) THEN s.hist ELSE application[n].hist
       IN /\ application'=[application EXCEPT ![n].hist=h, ![n].config=ConfigOf(h),
                    ![n].jobs[1].snapshot=EmptySnapshot]
          /\ history'=Observe([history EXCEPT !.applied=@\cup {h}],raft,disk,"ApplySnapshot")
    /\ UNCHANGED <<raft,disk,ready,requests,wire>>
\* README.md:120; callback occurs in ordered application, independent of Advance.
ProtocolApplyEntry(n,timeout) ==
    /\ Live(n) /\ application[n].jobs# <<>>
    /\ Head(application[n].jobs).snapshot.index=0
    /\ Head(application[n].jobs).entries# <<>>
    /\ LET e==Head(Head(application[n].jobs).entries)
           h==IF e.index<=Len(application[n].hist) THEN application[n].hist
              ELSE Append(application[n].hist,e)
           a==IF e.kind\in ConfKinds THEN ApplyConfCore(raft[n],e,timeout) ELSE raft[n]
           b0==IF e.kind\in ConfKinds THEN [a EXCEPT !.cfgHist=IF e.index>Len(a.cfgHist) THEN Prefix(h,e.index) ELSE @] ELSE a
           b==WrapperLoop(IF n\notin RawNodes /\ n\in Members(raft[n]) /\ n\notin Members(b0)
                  THEN [b0 EXCEPT !.propcEnabled=FALSE] ELSE b0)
       IN /\ e.index<=Len(application[n].hist)+1
          /\ raft'=[raft EXCEPT ![n]=b]
          /\ application'=[application EXCEPT ![n].hist=h, ![n].config=ConfigOf(h),
                        ![n].jobs[1].entries=Tail(@)]
          /\ history'=Observe([history EXCEPT !.applied=@\cup {h}],raft',disk,"ApplyEntry")
    /\ UNCHANGED <<disk,ready,requests,wire>>
ProtocolFinishApplication(n) ==
    /\ Live(n) /\ application[n].jobs# <<>>
    /\ Head(application[n].jobs).snapshot.index=0 /\ Head(application[n].jobs).entries= <<>>
    /\ application'=[application EXCEPT ![n].jobs=Tail(@)]
    /\ UNCHANGED <<raft,disk,ready,requests,wire,history>>
\* Caller-level durable application checkpoint; custom InitialState mode uses it.
ProtocolSaveApplication(n) ==
    /\ Live(n) /\ disk[n].savedApp#application[n].hist
    /\ disk'=[disk EXCEPT ![n].savedApp=application[n].hist]
    /\ history'=Observe(history,raft,disk',"SaveApplication")
    /\ UNCHANGED <<raft,ready,application,requests,wire>>
\* Application-defined write success requires actual application, not API nil.
ProtocolCompleteWrite(n,id) ==
    /\ Live(n) /\ id\in RequestId /\ requests[id].kind="Normal"
    /\ requests[id].handoff /\ ~requests[id].completed
    /\ \E k\in DOMAIN application[n].hist:application[n].hist[k].id=id
    /\ LET k==MinSet({p\in DOMAIN application[n].hist:application[n].hist[p].id=id})
           h==Prefix(application[n].hist,k)
       IN history'=Observe([history EXCEPT !.writes=@\cup {h},
             !.obligations=@\cup {[term |-> h[k].term,hist |-> h]},
             !.promises=@\cup {[message |-> Message("WriteResult",n,n,0),backed |-> DiskHas(disk[n],h)]}],raft,disk,"CompleteWrite")
    /\ requests'=[requests EXCEPT ![id].completed=TRUE]
    /\ UNCHANGED <<raft,disk,ready,application,wire>>
\* read_only.go:19-23 / node.go:63,168; caller fence only, no leadership guard.
ProtocolCompleteRead(n,id,k) ==
    /\ Live(n) /\ requests[id].kind="Read" /\ requests[id].node=n
    /\ requests[id].handoff /\ ~requests[id].completed
    /\ k\in DOMAIN application[n].reads
    /\ LET rd==application[n].reads[k]
           q==requests[id]
           result==[id |-> id, context |-> q.context, rd |-> rd,
                     app |-> application[n].hist, beforeWrites |-> q.beforeWrites]
       IN /\ rd.id=q.context
          /\ IF ReadFence="Strict" THEN Len(application[n].hist)>rd.index
             ELSE Len(application[n].hist)>=rd.index
          /\ history'=Observe([history EXCEPT !.readResults=@\cup {result}],raft,disk,"CompleteRead")
    /\ requests'=[requests EXCEPT ![id].completed=TRUE]
    /\ UNCHANGED <<raft,disk,ready,application,wire>>

\* storage.go:188-210. Snapshot data/config are caller application witnesses.
ProtocolCreateSnapshot(n,k) ==
    /\ Live(n) /\ k\in 1..Len(application[n].hist)
    /\ k>raft[n].store.snapshot.index /\ k>=raft[n].store.cut
    \* Legal MemoryStorage caller bound (storage.go:198-200); application may
    \* otherwise run before StorageAppend makes the durable entries visible.
    /\ k<=Len(raft[n].store.hist)
    /\ LET r==raft[n]
           s==[index |-> k, term |-> IF k<=Len(r.store.hist) THEN r.store.hist[k].term ELSE 0,
               hist |-> Prefix(application[n].hist,k), config |-> ConfigOf(Prefix(application[n].hist,k))]
           a==IF k>Len(r.store.hist) THEN Fatal(r,"CreateSnapshot beyond lastIndex")
              ELSE [r EXCEPT !.store.snapshot=s]
       IN /\ raft'=[raft EXCEPT ![n]=a]
          /\ history'=Observe([history EXCEPT !.snapshots=@\cup {s}],raft',disk,"CreateSnapshot")
    /\ UNCHANGED <<disk,ready,application,requests,wire>>
\* Caller durability of locally created snapshot, separate from creation/compaction.
ProtocolPersistLocalSnapshot(n) ==
    /\ Live(n) /\ raft[n].store.snapshot.index>disk[n].snapshot.index
    /\ disk'=[disk EXCEPT ![n].snapshot=raft[n].store.snapshot]
    /\ history'=Observe(history,raft,disk',"PersistLocalSnapshot")
    /\ UNCHANGED <<raft,ready,application,requests,wire>>
\* storage.go:213-233; contract allows only released, snapshotted data to compact.
ProtocolCompact(n,k) ==
    /\ Live(n) /\ k\in (raft[n].store.cut+1)..raft[n].applied
    /\ k<=raft[n].store.snapshot.index /\ k<=Len(raft[n].store.hist)
    /\ CoreCall(n,[raft[n] EXCEPT !.store.cut=k],"Compact")
ProtocolSnapshotAvailability(n,available) ==
    /\ Live(n) /\ raft[n].snapAvailable#available
    /\ CoreCall(n,[raft[n] EXCEPT !.snapAvailable=available],"SnapshotAvailability")
\* Volatile state, pending caller work and unpersisted writes are lost. Wire survives.
ProtocolCrash(n) ==
    /\ raft[n].alive
    /\ raft'=[raft EXCEPT ![n].alive=FALSE, ![n].out=EmptyBag]
    /\ ready'=[ready EXCEPT ![n]=EmptyReady]
    /\ application'=[application EXCEPT ![n]=EmptyApp]
    /\ history'=Observe(history,raft',disk,"Crash")
    /\ UNCHANGED <<disk,requests,wire>>
ProtocolStop(n) ==
           ProtocolCrash(n)
\* raft.go:322-375, confchange/restore.go:22-154. Construction atomically
\* reconstructs all incoming/outgoing voter, learner, staged learner and
\* auto-leave state before loading HardState.
\* UPDATE-MAP
\* code: raft.go:newRaft; confchange/restore.go:Restore
\* update: Update!AffectedRecoveryActions
RestartCore(n,timeout) ==
    LET d==disk[n] h==DiskHist(d)
        app==IF RecoveryMode="AppliedAdapter" THEN d.savedApp ELSE d.snapshot.hist
        fullCfg==IF RecoveryMode="AppliedAdapter" THEN ConfigOf(app) ELSE d.snapshot.config
        cfg==RestoreProjection(fullCfg)
        baseR==[InitialRaft(n,timeout) EXCEPT !.incarnation=raft[n].incarnation+1,
          !.term=d.hs.term, !.vote=d.hs.vote, !.config=cfg, !.cfgHist=app,
          !.store=Store(h,d.snapshot,d.snapshot.index,d.hs), !.unstable= <<>>,
          !.uoff=Len(h)+1, !.commit=d.snapshot.index, !.applied=d.snapshot.index,
          !.prs=[p\in VoterIDs(cfg)\cup cfg.learners |-> Progress(0,1,FALSE)]]
        a==IF d.hs=EmptyHS THEN baseR ELSE
             IF d.hs.commit<d.snapshot.index \/ d.hs.commit>Len(h)
             THEN Fatal(baseR,"loadState commit out of range")
             ELSE [baseR EXCEPT !.term=d.hs.term, !.vote=d.hs.vote, !.commit=d.hs.commit]
        b==IF a.fatal#"" THEN a ELSE AppliedTo(a,Len(app))
        c==BecomeFollower(b,b.term,0,timeout)
    IN [c EXCEPT !.prevHS=HS(c), !.prevSS=SS(c)]
ProtocolRestart(n,timeout) ==
    /\ ~raft[n].alive
    /\ LET a==RestartCore(n,timeout) d==disk[n]
           app==IF RecoveryMode="AppliedAdapter" THEN d.savedApp ELSE d.snapshot.hist
       IN /\ raft'=[raft EXCEPT ![n]=a]
          /\ application'=[application EXCEPT ![n]=[EmptyApp EXCEPT !.hist=app, !.config=ConfigOf(app)]]
          /\ history'=Observe([history EXCEPT !.recovery=@\cup
              {[savedTerm |-> d.hs.term, savedVote |-> d.hs.vote, term |-> a.term, vote |-> a.vote,
                commit |-> a.commit, hist |-> Hist(a), fatal |-> a.fatal,
                expectedConfig |-> IF RecoveryMode="AppliedAdapter" THEN ConfigOf(app) ELSE d.snapshot.config,
                config |-> a.config, diskHist |-> DiskHist(d), app |-> app]}],raft',disk,"Restart")
    /\ UNCHANGED <<disk,ready,requests,wire>>

(***************************************************************************
Independent safety contracts. Ghost observations never guard core actions.
Properties are reusable over all scenarios, including crashes and snapshots.
***************************************************************************)
\* Brief §5; source: raft.go:693-726, quorum/majority.go:170-201.
\* REQ-EVIDENCE ElectionSafety
\* intent:   In any term, at most one node ever wins an election and becomes leader.
\* status:   requirement
\* evidence: protocol Raft-paper §5.2 "at most one leader can be elected in a given term" -> the whole intent
\* evidence: test source/raft_paper_test.go:234 TestFollowerVote "each follower will vote for at most one" -> each node votes at most once per term (mechanism)
\* evidence: comment source/quorum/joint.go:18 "Decisions require the support of both majorities." -> a win needs majorities, which overlap (mechanism)
\* evidence: impl source/raft.go:925 "We can vote if this is a repeat of a vote we've already cast..."
\* evidence: impl source/raft.go:1269 "case quorum.VoteWon:"
\* watch:    raft.go:Step (MsgVote/MsgPreVote); raft.go:stepCandidate; raft.go:poll; tracker/tracker.go:RecordVote; tracker/tracker.go:TallyVotes; quorum/joint.go:VoteResult; quorum/majority.go:VoteResult
\* verified: V02
\* note:     protocol quote is Figure 3 of the Raft paper referenced at source/README.md:5 (not a workspace file); wins are ghost records made in base.tla BecomeLeader.
\* review:   retyped raft.go:925 to impl (it narrates the canVote expression); intent and status unchanged.
ElectionSafety == \A a,b\in history.wins:a.term=b.term => a.node=b.node
\* REQ-EVIDENCE LogMatching
\* intent:   If two nodes' logs hold an entry with the same index and the same nonzero term, the logs are identical up to that index.
\* status:   requirement
\* evidence: protocol Raft-paper §5.3 "if two logs contain an entry with the same index and term" -> the whole intent
\* evidence: test source/raft_paper_test.go:597 TestFollowerCheckMsgApp "entry in its log with the same index and term as the one" -> the append consistency check that maintains it (mechanism)
\* evidence: comment source/log.go:124 "An entry is considered to be conflicting if it has the same index" -> entries with the same index but different terms conflict (mechanism)
\* evidence: impl source/log.go:89 "if l.matchTerm(index, logTerm) {"
\* watch:    log.go:maybeAppend; log.go:findConflict; log.go:matchTerm; log_unstable.go:truncateAndAppend; raft.go:handleAppendEntries; raft.go:maybeSendAppend; raft.go:restore
\* verified: V02
\* note:     protocol quote is Figure 3 of the Raft paper (source/README.md:5); Hist includes compacted ghost prefixes, so the check also covers snapshot-covered positions.
\* review:   ok
LogMatching == \A n,p\in Server:
    \A k\in 1..Min(Last(raft[n]),Last(raft[p])):
       (Hist(raft[n])[k].term=Hist(raft[p])[k].term /\ Hist(raft[n])[k].term>0)
          => Prefix(Hist(raft[n]),k)=Prefix(Hist(raft[p]),k)
\* REQ-EVIDENCE LeaderCompleteness
\* intent:   Every leader elected in a term later than a recorded commitment's term has that committed history as a prefix of its log.
\* status:   requirement
\* evidence: protocol Raft-paper §5.4 "that entry will be present in the logs of the leaders for all higher-numbered terms" -> the whole intent
\* evidence: test source/raft_paper_test.go:820 TestVoter "denies its vote if its own log is more up-to-date" -> votes go only to candidates with up-to-date logs (mechanism)
\* evidence: test source/raft_paper_test.go:866 TestLeaderOnlyCommitsLogFromCurrentTerm "current term are committed by counting replicas" -> only current-term entries are committed by counting (mechanism)
\* evidence: comment source/log.go:275 "If the logs have last entries with different terms, then the log with the" -> definition of up-to-date used by the vote check (mechanism)
\* evidence: impl source/log.go:292 "if maxIndex > l.committed && l.zeroTermOnErrCompacted(l.term(maxIndex)) == term {"
\* watch:    log.go:isUpToDate; log.go:maybeCommit; raft.go:Step (MsgVote); raft.go:becomeLeader; raft.go:maybeCommit
\* verified: V02
\* note:     obligations are ghosts: durable-quorum commits (DurableObligations), published commit indexes (ProtocolPublish) and completed writes (ProtocolCompleteWrite); protocol quote from Raft paper Figure 3.
\* review:   ok
LeaderCompleteness == \A w\in history.wins:\A c\in history.obligations:
                         w.term>c.term => Covers(w.hist,c.hist)
\* REQ-EVIDENCE CommittedHistory
\* intent:   Committed history never diverges: a live node never loses its own committed prefix, all recorded commitments are pairwise compatible, and every live node's committed prefix is compatible with them.
\* status:   requirement
\* evidence: protocol Raft-paper §5.4.3 "no other server will ever apply a different log entry for the same index" -> recorded commitments and committed prefixes never diverge
\* evidence: comment source/log.go:200 "never decrease commit" -> a node's commit index never moves back
\* evidence: test source/log_test.go:450 TestCommitTo "never decrease" -> commitTo never lowers the commit index
\* evidence: impl source/log.go:95 "entry %d conflict with committed entry [committed(%d)]"
\* watch:    log.go:maybeAppend; log.go:commitTo; log.go:append; log_unstable.go:truncateAndAppend; raft.go:handleAppendEntries; raft.go:handleHeartbeat; raft.go:restore; raft.go:loadState
\* verified: V02
\* note:     liveOK and obligations are ghost observations (base.tla SetCore, ProtocolReceive, DurableObligations, ProtocolPublish, ProtocolCompleteWrite); protocol quote from Raft paper Figure 3. The commit-index evidence covers only the index part of "never loses its committed prefix"; the content part rests on the protocol line.
\* review:   removed TestNodeCommitPaginationAfterRestart, which asserts commit non-regression across a restart while liveOK is checked within one live incarnation; intent and status unchanged.
CommittedHistory == /\ history.liveOK
    /\ \A a,b\in history.obligations:Compatible(a.hist,b.hist)
    /\ \A n\in Server:\A c\in history.obligations:
         raft[n].alive => Compatible(Prefix(Hist(raft[n]),raft[n].commit),c.hist)
\* REQ-EVIDENCE AppliedAgreement
\* intent:   Any two application histories ever applied, on any nodes, are prefix-compatible.
\* status:   requirement
\* evidence: protocol Raft-paper §5.4.3 "no other server will ever apply a different log entry for the same index" -> the whole intent
\* evidence: test source/raft_paper_test.go:545 TestFollowerCommitEntry "it applies the entry to its local state machine (in log order)" -> entries are handed out for application in log order
\* evidence: comment source/node.go:155 "No committed entries from the next Ready may be applied until all committed entries" -> application proceeds in order, so each node's history is a prefix sequence
\* evidence: doc source/README.md:122 "all updates must be processed in the order they were returned by Ready" -> application proceeds in Ready order
\* watch:    log.go:nextEnts; node.go:newReady; raft.go:advance; log.go:appliedTo; raft.go:restore
\* verified: V02
\* note:     application histories are produced by the caller model (ProtocolApplyEntry, ProtocolApplySnapshot, ProtocolRestart); protocol quote from Raft paper Figure 3.
\* review:   ok
AppliedAgreement == \A a,b\in history.applied:Compatible(a,b)
\* Durable term/vote promises survive constructor; no equality to volatile votes.
\* REQ-EVIDENCE VoteRecovery
\* intent:   After a restart a node's term is at least its durably saved term, and while still in that term it keeps the durably saved vote.
\* status:   requirement
\* evidence: comment source/node.go:579 "(Updated on stable storage before responding to RPCs)" -> term and vote are persistent state that survives restart
\* evidence: comment source/node.go:58 "The current state of a Node to be saved to stable storage BEFORE" -> the HardState (term, vote) is durably saved
\* evidence: doc source/README.md:118 "no messages be sent until the latest HardState has been persisted to disk" -> the persisted HardState is the one acted upon
\* evidence: impl source/raft.go:1539 "r.Term = state.Term"
\* watch:    raft.go:newRaft; raft.go:loadState; raft.go:becomeFollower; raft.go:reset; node.go:MustSync; storage.go:InitialState
\* verified: V02
\* note:     node.go:578-582 restates Raft Figure 2 persistent state (currentTerm, votedFor); recovery records are ghosts made in base.tla ProtocolRestart.
\* review:   ok
VoteRecovery == \A x\in history.recovery:
    x.term>=x.savedTerm /\ (x.term=x.savedTerm /\ x.savedVote#0 => x.vote=x.savedVote)
\* REQ-EVIDENCE RecoveryBacking
\* intent:   On restart the loaded commit index refers only to locally persisted, non-missing entries.
\* status:   mixed
\* evidence: doc source/README.md:116 "Write Entries, HardState and Snapshot to persistent storage in order" -> a persisted commit index never runs ahead of persisted entries
\* evidence: doc source/README.md:124 "all persisted log entries must be made available via an implementation of the Storage" -> the entries up to the loaded commit are available (not missing)
\* evidence: impl source/raft.go:1536 "%x state.commit %d is out of range [%d, %d]"
\* watch:    raft.go:newRaft; raft.go:loadState; log.go:newLogWithSize; log.go:appliedTo; storage.go:InitialState; storage.go:Append
\* verified: V02
\* note:     README.md:116 orders Entries before HardState, which is what makes a persisted commit index refer to persisted entries.
\* clause commit<=Len(diskHist) and no Missing entry up to commit: requirement — README.md:116, README.md:124
\* clause Covers(diskHist,app): model-internal — relates the caller model's recovered application state (RecoveryMode Replay or AppliedAdapter) to the disk log; raft.go:147 (Config.Applied) and TestNodeCommitPaginationAfterRestart say nothing about this prefix relation
\* relabel:  requirement -> mixed (clause statuses: model-internal, requirement); handle clause by clause
\* review:   narrowed the intent to the two commit clauses and recorded the application-prefix clause as model-internal; removed raft.go:147 and TestNodeCommitPaginationAfterRestart, which support neither commit clause.
RecoveryBacking == \A x\in history.recovery:
    /\ x.commit<=Len(x.diskHist)
    /\ \A k\in 1..x.commit:x.diskHist[k].kind#"Missing"
    /\ Covers(x.diskHist,x.app)
\* REQ-EVIDENCE PromiseBacking
\* intent:   Every message a node sends is backed by durable state: its term and granted vote are persisted, and the entries it acknowledges and the commit prefix it advertises are on its disk.
\* status:   mixed
\* evidence: doc source/README.md:118 "no messages be sent until the latest HardState has been persisted to disk" -> term and granted vote persisted before any message is sent
\* evidence: comment source/node.go:81 "Messages specifies outbound messages to be sent AFTER Entries are" -> acknowledged entries (and so any advertised commit prefix of the local log) are on disk
\* evidence: comment source/node.go:69 "Entries specifies entries to be saved to stable storage BEFORE" -> entries are persisted before messages are sent
\* evidence: comment source/node.go:579 "(Updated on stable storage before responding to RPCs)" -> term, vote and log entries are persisted before responding
\* evidence: impl source/node.go:583 "return entsnum != 0 || st.Vote != prevst.Vote || st.Term != prevst.Term"
\* watch:    node.go:newReady; node.go:MustSync; rawnode.go:Ready; rawnode.go:acceptReady; raft.go:send; raft.go:handleAppendEntries; raft.go:handleSnapshot
\* verified: V02
\* note:     README.md:118 also says messages "may be sent while entries from the same batch are being persisted" (SendPolicy SameBatch); this property still requires disk backing at publish time, see out/concerns.md.
\* clause message promises (PromiseOK: term, granted vote, acknowledged entries, advertised commit): requirement — README.md:118, node.go:58, node.go:69, node.go:81
\* clause WriteResult promise (a completed application write is on the local disk): unknown — node.go:77 says committed entries were "committed to stable store", not that they are on the local disk, and README.md:114 lets steps 1-3 run in parallel; ghost made in base.tla ProtocolCompleteWrite
\* relabel:  requirement -> mixed (clause statuses: requirement, unknown); handle clause by clause
\* review:   narrowed the intent from "message or write result" to messages, because no non-impl source says a completed application write must be on the local disk; recorded that as an unknown clause.
PromiseBacking == \A p\in history.promises:p.backed
\* README.md:120,193. Configuration has a committed/constructor/snapshot origin.
\* REQ-EVIDENCE ConfigurationOrigin
\* intent:   A live node's active configuration is exactly the result of the configuration entries in a history that is a prefix of its log and lies within its committed prefix.
\* status:   requirement
\* evidence: doc source/README.md:193 "the membership change takes effect when its entry is applied" -> the active configuration is the result of applied configuration entries
\* evidence: proto source/raftpb/raft.proto:148 "configuration changes become active when they are *applied* to the" -> the active configuration is the result of applied configuration entries
\* evidence: doc source/README.md:178 "After config change is committed, some committed entry with type raftpb.EntryConfChange" -> only committed configuration entries are applied
\* evidence: comment source/log.go:37 "Invariant: applied <= committed" -> the applied history lies within the committed prefix
\* evidence: impl source/raft.go:1463 "func (r *raft) applyConfChange(cc pb.ConfChangeV2) pb.ConfState {"
\* watch:    raft.go:applyConfChange; raft.go:switchToConfig; raft.go:restore; raft.go:newRaft; confchange/restore.go:Restore; bootstrap.go:Bootstrap; node.go:run (confc)
\* verified: V02
\* note:     cfgHist is a model ghost (set in base.tla ProtocolApplyEntry, Restore, RestartCore) and ConfigOf is the model's independent configuration oracle.
\* review:   ok
ConfigurationOrigin == \A n\in Server:
    raft[n].alive =>
       /\ raft[n].config=ConfigOf(raft[n].cfgHist)
       /\ Covers(Hist(raft[n]),raft[n].cfgHist)
       /\ Len(raft[n].cfgHist)<=raft[n].commit
\* Each configuration entry must commit using its predecessor voter configuration.
\* Bootstrap entries (id=0) are explicit constructor axioms, not quorum decisions.
\* REQ-EVIDENCE ConfigurationTransitionSafety
\* intent:   Whenever a leader newly commits a request-originated configuration entry, it counts that commit under the configuration produced by all entries before it.
\* status:   requirement
\* evidence: doc source/README.md:193 "the entry is committed under the old membership instead of the new" -> the entry is committed under the configuration before it
\* evidence: doc source/README.md:195 "any proposed membership change is simply disallowed while any uncommitted change appears" -> all earlier configuration entries are already in effect, so the old membership is the one produced by all earlier entries
\* evidence: comment source/raft.go:281 "Only one conf change may be pending (in the log, but not yet" -> at most one configuration entry is pending at a time
\* evidence: test source/raft_test.go:3043 TestStepIgnoreConfig "EntryConfChange type when the first one is uncommitted, the node will set" -> a second pending configuration proposal is neutralised
\* evidence: impl source/raft.go:1031 "if r.pendingConfIndex > r.raftLog.applied {"
\* watch:    raft.go:stepLeader (MsgProp, pendingConfIndex); raft.go:becomeLeader; raft.go:advance (auto-leave); raft.go:applyConfChange; raft.go:switchToConfig; tracker/tracker.go:Committed
\* verified: V02
\* note:     entries with id=0 are skipped; that excludes bootstrap entries and also the auto-leave entry appended by Advance (see out/concerns.md). commitUses are ghost records made in base.tla MaybeCommit.
\* review:   ok
ConfigurationTransitionSafety == \A c\in history.commitUses:
    \A k\in (c.oldCommit+1)..Len(c.hist):
       (c.hist[k].kind\in ConfKinds /\ c.hist[k].id#0) =>
             c.config=ConfigOf(Prefix(c.hist,k-1))
\* Learners may grant votes after revision 46580dcf; they remain ineligible to
\* originate campaigns, and QuorumAccounting constrains decision-side counting.
\* REQ-EVIDENCE LearnerEligibility
\* intent:   A node that is a learner in its own configuration never starts a (pre-)campaign.
\* status:   requirement
\* evidence: test source/raft_test.go:3921 TestLearnerCampaign "a learner won't campaign even if it receives" -> a learner does not campaign on MsgHup or MsgTimeoutNow
\* evidence: test source/raft_test.go:318 TestLearnerElectionTimeout "Learner should not start election even when times out." -> a learner does not campaign on election timeout
\* evidence: history db54973bb (raft: prevent learners from becoming leader) "there was no safeguard against an explicit call to `Campaign()`." -> a learner must not campaign even on an explicit Campaign call
\* evidence: comment source/raft.go:127 "It does not vote or promote itself." -> a learner does not promote itself
\* evidence: impl source/raft.go:1460 "return pr != nil && !pr.IsLearner"
\* watch:    raft.go:promotable; raft.go:Step (MsgHup); raft.go:tickElection; raft.go:stepFollower (MsgTimeoutNow); raft.go:campaign; raft.go:switchToConfig
\* verified: V02
\* note:     raft.go:127 also says learners do not vote, which is stale since abb533c27 (learners may grant votes); see out/concerns.md.
\* review:   ok
LearnerEligibility == \A x\in history.campaigns:~x.learner
\* REQ-EVIDENCE QuorumAccounting
\* intent:   Every election win and every commit decision is backed by a majority of each half of a non-empty (joint) voter configuration, counting only voters.
\* status:   requirement
\* evidence: comment source/quorum/joint.go:18 "Decisions require the support of both majorities." -> a majority of each half
\* evidence: proto source/raftpb/raft.proto:156 "in which quorum requires a majority of both the pre-changes and post-changes" -> a majority of each half in a joint configuration
\* evidence: comment source/tracker/tracker.go:176 "the voting members of the group have acknowledged" -> commit counts only voters
\* evidence: test source/raft_paper_test.go:472 TestLeaderAcknowledgeCommit "has replicated it on a majority of the servers" -> commit needs a majority
\* evidence: history 60429a913 (raft: internally support joint consensus) "of empty commit quorums, which was previously possible but for no good" -> the incoming voter configuration is non-empty
\* evidence: test source/confchange/testdata/simple_safety.txt:4 TestConfChangeDataDriven "removed all voters" -> a change that empties the voters is rejected
\* evidence: impl source/confchange/confchange.go:176 "removed all voters"
\* watch:    tracker/tracker.go:Committed; tracker/tracker.go:TallyVotes; quorum/joint.go:CommittedIndex; quorum/joint.go:VoteResult; quorum/majority.go:CommittedIndex; quorum/majority.go:VoteResult; raft.go:poll; raft.go:maybeCommit
\* verified: V02
\* note:     quorum/majority.go lets an empty half win by convention (majority.go:180-183); the property additionally requires the incoming voter set to be non-empty, which 60429a913 ("prevent the use of empty commit quorums") states as a rule. Found with hist.sh log -S'removed all voters' -- confchange/confchange.go.
\* review:   the non-empty voter clause had only impl evidence; added history 60429a913 and the simple_safety.txt test that state it, so status stays requirement.
QuorumAccounting ==
    /\ \A w\in history.wins:w.config.voters#{} /\ JointWon(w.config,w.yes)
    /\ \A c\in history.commitUses:c.config.voters#{} /\
         c.matches\subseteq VoterIDs(c.config) /\ JointWon(c.config,c.matches)
\* raft.go:613 versus 1039-1091: distinguish self's volatile evidence.
\* REQ-EVIDENCE ReplicationEvidence
\* intent:   For every peer whose Match a live leader records as positive, that peer acknowledged a log whose prefix up to Match equals the leader's own log prefix.
\* status:   requirement
\* evidence: doc source/design.md:7 "is the index of the highest known matched entry" -> Match names an index up to which the peer's log is known to match the leader's
\* evidence: comment source/tracker/progress.go:139 "MaybeUpdate is called when an MsgAppResp arrives from the follower, with the" -> Match only advances to an index the follower acknowledged
\* evidence: impl source/raft.go:1105 "if pr.MaybeUpdate(m.Index) {"
\* watch:    tracker/progress.go:MaybeUpdate; raft.go:stepLeader (MsgAppResp); raft.go:handleAppendEntries; raft.go:handleSnapshot; raft.go:reset; raft.go:appendEntry
\* verified: V02
\* note:     the leader's own entry is excluded (volatile self Match, raft.go:652); the acknowledged log is a ghost witness carried in MsgAppResp (base.tla HandleAppendEntries/HandleSnapshot).
\* review:   ok
ReplicationEvidence == \A n\in Server:
    raft[n].alive /\ raft[n].role="Leader" =>
      \A p\in Members(raft[n])\{n}:
       LET pr==raft[n].prs[p] IN
       pr.match>0 => /\ Len(pr.evidence)>=pr.match
                    /\ Covers(Hist(raft[n]),Prefix(pr.evidence,pr.match))
SnapshotValid(s) == s.index=Len(s.hist) /\ s.config=ConfigOf(s.hist) /\
                    (s.index>0 => s.hist[s.index].term=s.term)
\* REQ-EVIDENCE SnapshotBacking
\* intent:   Every snapshot created, held as unstable, or persisted describes exactly the history up to its index: its last term and configuration agree with that history.
\* status:   mixed
\* evidence: comment source/storage.go:191 "the result of the last ApplyConfChange must be passed in." -> the snapshot's configuration agrees with the history up to its index
\* evidence: comment source/node.go:173 "Returns an opaque non-nil ConfState protobuf which must be recorded in" -> the snapshot's configuration is the applied one
\* evidence: comment source/storage.go:189 "can be used to reconstruct the state at that point." -> the snapshot describes the history up to its index (including its last term)
\* evidence: impl source/storage.go:205 "ms.snapshot.Metadata.Term = ms.ents[i-offset].Term"
\* watch:    storage.go:CreateSnapshot; storage.go:ApplySnapshot; raft.go:restore; log_unstable.go:restore; node.go:ApplyConfChange; raft.go:applyConfChange
\* verified: V02
\* note:     snapshot data and ConfState are produced by the caller model (ProtocolCreateSnapshot).
\* clause s.config=ConfigOf(s.hist) and last term matches: requirement — storage.go:189-191, node.go:173
\* clause s.index=Len(s.hist): model-internal — ghost well-formedness of the snapshot record
\* relabel:  requirement -> mixed (clause statuses: model-internal, requirement); handle clause by clause
\* review:   moved the ghost well-formedness condition from note into a model-internal clause line so the block's single status no longer covers it silently.
SnapshotBacking ==
    /\ \A s\in history.snapshots:SnapshotValid(s)
    /\ \A n\in Server:SnapshotValid(raft[n].usnap) /\ SnapshotValid(disk[n].snapshot)
\* REQ-EVIDENCE AckPreservation_LogUnchanged
\* intent:   Advance leaves the log history unchanged, except that it may append exactly one empty ConfChangeV2 (auto-leave) entry.
\* status:   impl-abstraction
\* evidence: impl source/raft.go:565 "configuration should be auto-left, initiate that now."
\* evidence: impl source/raft.go:574 "if !r.appendEntry(ent) {"
\* evidence: impl source/log_unstable.go:85 "if gt == t && i >= u.offset {"
\* watch:    raft.go:advance; log.go:stableTo; log_unstable.go:stableTo; rawnode.go:Advance
\* verified: V02
\* note:     searched README.md, doc.go, node.go/rawnode.go Advance docs and history (hist.sh show 46580dcf6, which added the auto-leave append): nothing states that Advance must not change the log; it describes this revision's Advance.
\* review:   retyped raft.go:565 from comment to impl (it narrates the next statements, "initiate that now"); status unchanged.
AckPreservation_LogUnchanged == \A a\in history.acks:
    /\ \/ a.before=a.after
       \/ /\ Len(a.after)=Len(a.before)+1 /\ Prefix(a.after,Len(a.before))=a.before
          /\ LET e==a.after[Len(a.after)] IN e.kind="V2" /\ e.changes= <<>>
\* REQ-EVIDENCE AckPreservation_SnapshotRetained
\* intent:   Advance does not discard a pending unstable snapshot other than the one handed out in the acknowledged Ready.
\* status:   unknown
\* evidence: impl source/log_unstable.go:112 "if u.snapshot != nil && u.snapshot.Metadata.Index == i {"
\* evidence: impl source/raft.go:592 "r.raftLog.stableSnapTo(rd.Snapshot.Metadata.Index)"
\* watch:    log_unstable.go:stableSnapTo; raft.go:advance; raft.go:restore; log_unstable.go:restore
\* verified: V02
\* note:     looks like a correctness requirement (the snapshot analogue of the dropped-message bug described in 5fa684b47), but only impl evidence was found. Searched hist.sh log -S'stableSnapTo' (46580dcf6, c60f8da6b, 4b3a7ff35, 83245f7fe) and hist.sh show 83245f7fe: every change only moves the index-equality check; no comment, doc or test states the rule.
\* review:   ok
AckPreservation_SnapshotRetained == \A a\in history.acks:
    /\ (a.oldSnap#0 /\ a.oldSnap#a.batchSnap => a.afterSnap=a.oldSnap)
\* REQ-EVIDENCE AckPreservation_AppliedCursor
\* intent:   When the acknowledged Ready carried committed entries or a snapshot, Advance sets the applied index to exactly that Ready's cursor.
\* status:   requirement
\* evidence: comment source/node.go:112 "appliedCursor extracts from the Ready the highest index the client has" -> after Advance the applied index is the Ready's cursor
\* evidence: comment source/node.go:159 "Advance notifies the Node that the application has saved progress up to the last Ready." -> Advance records progress up to exactly the last Ready
\* evidence: test source/rawnode_test.go:732 TestRawNodeCommitPaginationAfterRestart "its internal applied index cursor to 10 (when it should be 9)" -> the applied index must equal the last applied entry, not more
\* evidence: impl source/raft.go:562 "r.raftLog.appliedTo(index)"
\* watch:    node.go:appliedCursor; raft.go:advance; log.go:appliedTo; rawnode.go:Advance; node.go:run (advancec)
\* verified: V02
\* review:   ok
AckPreservation_AppliedCursor == \A a\in history.acks:
    /\ (a.cursor#0 => a.applied=a.cursor)
\* REQ-EVIDENCE AckPreservation_OutputPreserved
\* intent:   Advance does not drop outgoing messages that were produced after the Ready was accepted.
\* status:   mixed
\* evidence: history 5fa684b47 (raft: require app to consume result from Ready()) "`someMsg` would be dropped, because `Advance()` would clear out the" -> Advance must not drop messages produced after the Ready
\* evidence: test source/rawnode_test.go:954 TestRawNodeConsumeReady "Add a message to raft to make sure that Advance() doesn't drop it." -> Advance does not drop a later message
\* evidence: comment source/rawnode.go:121 "The returned Ready() *must* be handled and subsequently" -> output is handed over at Ready, not at Advance
\* evidence: impl source/rawnode.go:176 "rn.raft.advance(rd)"
\* watch:    rawnode.go:Advance; rawnode.go:acceptReady; raft.go:advance; node.go:run (readyc/advancec)
\* verified: V02
\* note:     the formula checks equality (outAfter=outBefore, readsAfter=readsBefore, ssAfter=ssBefore), which is stronger than "does not drop messages".
\* clause outAfter=outBefore beyond "no message dropped" (Advance adds no message): impl-abstraction — raft.go:552-594 sends nothing; no source requires it
\* clause readsAfter=readsBefore: unknown — read states follow the same accept-at-Ready code (rawnode.go:138-146), but 5fa684b47 and the test speak only of messages
\* clause ssAfter=ssBefore: impl-abstraction — node.go:55 "It is not required to consume or store SoftState"; nothing says Advance must keep it
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, unknown); handle clause by clause
\* review:   narrowed the intent from "never drops or alters messages, read states or SoftState" to "does not drop later messages", the only part the commit message and test state; recorded the other equalities as clause lines.
AckPreservation_OutputPreserved == \A a\in history.acks:
    /\ a.outAfter=a.outBefore
    /\ a.readsAfter=a.readsBefore
    /\ a.ssAfter=a.ssBefore
\* REQ-EVIDENCE AckPreservation
\* intent:   conjunction of the parts below; kept so existing configs and references still work
\* status:   model-internal
\* verified: V02
\* note:     split by origin into AckPreservation_LogUnchanged (impl-abstraction), AckPreservation_SnapshotRetained (unknown), AckPreservation_AppliedCursor (requirement), AckPreservation_OutputPreserved (requirement, with impl-abstraction/unknown clause lines)
\* review:   noted that AckPreservation_OutputPreserved now carries clause lines; otherwise ok.
AckPreservation == AckPreservation_LogUnchanged /\ AckPreservation_SnapshotRetained /\
                   AckPreservation_AppliedCursor /\ AckPreservation_OutputPreserved
\* REQ-EVIDENCE ReadyAccounting_NoLostReads
\* intent:   The ghost set of lost read states stays empty.
\* status:   model-internal
\* verified: V02
\* note:     history.lostReads is initialised to {} in EmptyHistory and no action ever updates it, so this clause is vacuous (out/concerns.md).
\* review:   ok
ReadyAccounting_NoLostReads ==
    /\ history.lostReads={}
\* REQ-EVIDENCE ReadyAccounting_CommittedPage
\* intent:   Each Ready's committed-entry page starts right after the applied index (or at the first available index), is contiguous, ends at the Ready's cursor and never passes the commit index; a Ready without entries uses the snapshot index as cursor.
\* status:   requirement
\* evidence: test source/rawnode_test.go:785 TestRawNodeCommitPaginationAfterRestart "attempting to apply index %d after index %d, leaving a gap" -> each page starts right after the previously applied index
\* evidence: comment source/log.go:149 "If applied is smaller than the index of snapshot, it returns all committed" -> after a snapshot the page starts at the first available index
\* evidence: comment source/node.go:77 "These have previously been committed to stable" -> the page never passes the commit index
\* evidence: comment source/node.go:112 "appliedCursor extracts from the Ready the highest index the client has" -> the cursor is the last entry's index, or the snapshot index without entries
\* evidence: impl source/log.go:152 "off := max(l.applied+1, l.firstIndex())"
\* watch:    log.go:nextEnts; log.go:slice; util.go:limitSize; node.go:newReady; node.go:appliedCursor; storage.go:Entries
\* verified: V02
\* review:   ok
ReadyAccounting_CommittedPage ==
    /\ \A b\in history.readyChecks:
        /\ b.cursor<=b.commit
        /\ IF b.entries= <<>> THEN b.cursor=b.snapshot ELSE
             /\ Head(b.entries).index=Max(b.from+1,b.first)
             /\ b.cursor=b.entries[Len(b.entries)].index
             /\ \A k\in DOMAIN b.entries:b.entries[k].index=Head(b.entries).index+k-1
\* REQ-EVIDENCE ReadyAccounting
\* intent:   conjunction of the parts below; kept so existing configs and references still work
\* status:   model-internal
\* verified: V02
\* note:     split by origin into ReadyAccounting_NoLostReads (model-internal), ReadyAccounting_CommittedPage (requirement)
\* review:   ok
ReadyAccounting == ReadyAccounting_NoLostReads /\ ReadyAccounting_CommittedPage
\* rawnode.go:119-146 and node.go:385-387: every delivered/public Ready accepts
\* messages, read states and SoftState; quota remains Advance-owned.
\* REQ-EVIDENCE ReadyOwnership_QuotaUntouched
\* intent:   Producing and accepting a Ready never changes the leader's uncommitted-size quota.
\* status:   impl-abstraction
\* evidence: impl source/raft.go:289 "prevent unbounded log growth. Only maintained by the leader. Reset on"
\* evidence: impl source/raft.go:585 "r.reduceUncommittedSize(rd.CommittedEntries)"
\* evidence: impl source/rawnode.go:138 "func (rn *RawNode) acceptReady(rd Ready) {"
\* watch:    rawnode.go:acceptReady; rawnode.go:Ready; node.go:newReady; raft.go:advance; raft.go:reduceUncommittedSize
\* verified: V02
\* note:     searched hist.sh log -S'reduceUncommittedSize' (2598fca29, a370b6f6e, c60f8da6b, 46580dcf6): the release point is Advance at V02, but nothing states that Ready must leave the quota alone.
\* review:   retyped raft.go:289 from comment to impl: it describes who maintains the field and says nothing about Ready leaving the quota alone; status unchanged.
ReadyOwnership_QuotaUntouched == \A b\in history.readyChecks:
    /\ b.quotaAfter=b.quotaBefore
\* REQ-EVIDENCE ReadyOwnership_OutputAccepted
\* intent:   Once a Ready is accepted (returned by RawNode.Ready or delivered by Node), its messages and read states are removed from the node's pending output.
\* status:   requirement
\* evidence: comment source/rawnode.go:121 "The returned Ready() *must* be handled and subsequently" -> the whole returned Ready (messages and read states) becomes the application's responsibility at Ready
\* evidence: test source/rawnode_test.go:945 TestRawNodeConsumeReady "Now call Ready() which should move the message into the Ready" -> messages are removed from pending output at Ready (messages only)
\* evidence: history 5fa684b47 (raft: require app to consume result from Ready()) "reestablishes the previous behavior (result of `Ready()` must" -> acceptance happens at Ready
\* evidence: impl source/rawnode.go:145 "rn.raft.msgs = nil"
\* watch:    rawnode.go:Ready; rawnode.go:acceptReady; rawnode.go:readyWithoutAccept; node.go:run (readyc)
\* verified: V02
\* note:     the test asserts the message case only; the read-state case rests on the general "must be handled" contract.
\* review:   ok
ReadyOwnership_OutputAccepted == \A b\in history.readyChecks:
    /\ b.outAfter=EmptyBag /\ b.readsAfter= <<>>
\* REQ-EVIDENCE ReadyOwnership
\* intent:   conjunction of the parts below; kept so existing configs and references still work
\* status:   model-internal
\* verified: V02
\* note:     split by origin into ReadyOwnership_QuotaUntouched (impl-abstraction), ReadyOwnership_OutputAccepted (requirement)
\* review:   ok
ReadyOwnership == ReadyOwnership_QuotaUntouched /\ ReadyOwnership_OutputAccepted
\* raft.go:554-581: every eligible Advance appends leave-joint or records the
\* quota-retry cursor. This checks the effect, not eventual scheduling.
\* REQ-EVIDENCE AutoLeaveAdvance
\* intent:   When a leader in an auto-leave joint configuration has applied the change that entered it, Raft initiates leaving the joint configuration by appending an empty ConfChangeV2 entry.
\* status:   mixed
\* evidence: proto source/raftpb/raft.proto:112 "If set, the config is joint and Raft will automatically transition into" -> Raft itself initiates leaving an auto-leave joint configuration
\* evidence: test source/rawnode_test.go:111 TestRawNodeProposeAndConfChange "joint configurations makes sure that they are exited successfully." -> auto-leave joint configurations are left by an empty ConfChangeV2
\* evidence: impl source/raft.go:565 "configuration should be auto-left, initiate that now."
\* evidence: impl source/raft.go:575 "If we could not append the entry, bump the pending conf index"
\* evidence: impl source/raft.go:563 "if r.prs.Config.AutoLeave && index >= r.pendingConfIndex && r.state == StateLeader {"
\* watch:    raft.go:advance; raft.go:appendEntry; raft.go:increaseUncommittedSize; tracker/tracker.go:Config (AutoLeave)
\* verified: V02
\* note:     the property checks the effect of each eligible Advance, not eventual leaving.
\* clause eligible Advance appends the empty V2 entry: requirement — raft.proto:112, rawnode_test.go:111
\* clause the append happens inside that same Advance call: impl-abstraction — raft.go:562-563 only
\* clause quota-retry branch (DropQuota sets pending to the last index): impl-abstraction — raft.go:575-579 is a narrating comment followed by "TODO(tbg): test this case."
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   retyped the two narrating raft.go comments (565, 575) to impl, narrowed the intent to Raft initiating the leave, and recorded the per-Advance timing and quota-retry branch as impl-abstraction clauses.
AutoLeaveAdvance == \A a\in history.autoLeaveChecks:
    a.eligible =>
      \/ /\ Len(a.afterHist)=a.beforeLast+1
         /\ a.afterHist[Len(a.afterHist)].kind="V2"
         /\ a.afterHist[Len(a.afterHist)].changes= <<>>
      \/ /\ a.decision="DropQuota" /\ a.pending=Len(a.afterHist)
\* tracker.Config shape and the source's persisted ConfState must survive a load.
\* REQ-EVIDENCE JointConfigurationShape
\* intent:   Every node's configuration is empty or well formed: non-empty incoming voters, learners disjoint from both voter halves, staged learners only among outgoing voters and disjoint from incoming voters and learners, and no staged learners or auto-leave outside a joint state.
\* status:   requirement
\* evidence: comment source/tracker/tracker.go:37 "Invariant: Learners and Voters does not intersect, i.e. if a peer is in" -> learners disjoint from both voter halves
\* evidence: comment source/confchange/confchange.go:297 "Any staged learner was staged because it could not be directly added due" -> staged learners are outgoing voters
\* evidence: proto source/raftpb/raft.proto:108 "These nodes are necessarily currently in nodes_joint (or they would have" -> staged learners only among outgoing voters, so none outside a joint state
\* evidence: proto source/raftpb/raft.proto:112 "If set, the config is joint and Raft will automatically transition into" -> no auto-leave outside a joint state
\* evidence: history 60429a913 (raft: internally support joint consensus) "of empty commit quorums, which was previously possible but for no good" -> non-empty incoming voters
\* evidence: test source/confchange/testdata/joint_learners_next.txt:1 TestConfChangeDataDriven "Verify that when a voter is demoted in a joint config, it will show up" -> a demoted voter is staged in learners_next, not added as learner while joint
\* evidence: impl source/confchange/confchange.go:329 "AutoLeave must be false when not joint"
\* watch:    confchange/confchange.go:checkInvariants; confchange/confchange.go:EnterJoint; confchange/confchange.go:LeaveJoint; confchange/confchange.go:makeLearner; confchange/confchange.go:apply; confchange/restore.go:Restore; raft.go:switchToConfig
\* verified: V02
\* note:     the empty configuration is allowed for joining nodes (confchange.go:279-284). The learners_next/incoming-voter disjointness follows from tracker.go:43-46 (staging exists because a demoted voter cannot be both voter and learner).
\* review:   non-empty incoming voters had only impl support; added history 60429a913 and raft.proto:112 (auto-leave implies joint), and rewrote the note that called that clause impl-only.
JointConfigurationShape == \A n\in Server:
    LET c==raft[n].config IN
    \/ c=EmptyConfig
    \/ /\ c.voters#{}
       /\ c.learners\cap VoterIDs(c)={}
       /\ c.learnersNext\subseteq c.outgoing
       /\ c.learnersNext\cap (c.voters\cup c.learners)={}
       /\ (c.outgoing={} => c.learnersNext={} /\ ~c.autoLeave)
\* REQ-EVIDENCE JointSnapshotRecovery
\* intent:   A joint configuration (outgoing voters, staged learners, auto-leave) survives intact both when a node restarts from a persisted ConfState and in the live configuration derived from its configuration history.
\* status:   requirement
\* evidence: history e515a6751 (raft: fix restoring joint configurations) "the joint configuration and was simply dropping it on the floor." -> restoring from a ConfState must keep the joint configuration
\* evidence: test source/confchange/restore_test.go:130 TestRestore "VotersOutgoing: ids(1, 2, 4, 6), LearnersNext: ids(4)" -> a joint ConfState round-trips through Restore
\* evidence: comment source/confchange/restore.go:112 "runs a sequence of changes enacting the configuration described in the" -> Restore enacts the full described configuration
\* evidence: proto source/raftpb/raft.proto:148 "configuration changes become active when they are *applied* to the" -> the live configuration is the one produced by the applied configuration history
\* evidence: impl source/raft.go:367 "assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, prs))"
\* watch:    confchange/restore.go:Restore; confchange/restore.go:toConfChangeSingle; raft.go:newRaft; raft.go:restore; raft.go:switchToConfig; util.go:assertConfStatesEquivalent; raftpb/confstate.go:Equivalent
\* verified: V02
\* note:     the live clause compares the active config with ConfigOf(cfgHist), a model ghost; RestoreProjection is the identity at V02.
\* review:   the live-configuration clause had no supporting line; added raft.proto:148 (already used for ConfigurationOrigin); intent and status unchanged.
JointSnapshotRecovery ==
    /\ \A x\in history.recovery:
         x.expectedConfig.outgoing#{} => x.config=x.expectedConfig
    /\ \A n\in Server:
         raft[n].alive /\ ConfigOf(raft[n].cfgHist).outgoing#{} =>
             raft[n].config=ConfigOf(raft[n].cfgHist)
\* raft.go:1398-1420 still recognizes only incoming voters and current learners
\* before the complete confchange.Restore call. A fresh nonmatching snapshot must
\* nevertheless be accepted for every legitimate joint member.
\* REQ-EVIDENCE JointSnapshotMemberAcceptance
\* intent:   A follower that belongs to a fresh snapshot's (joint) configuration, including as an outgoing-only voter, and does not already match it, must install it and adopt its full configuration.
\* status:   mixed
\* evidence: comment source/raft.go:1398 "More defense-in-depth: throw away snapshot if recipient is not in the" -> a snapshot is thrown away only when the recipient is not in its configuration, which "shouldn't ever happen"
\* evidence: proto source/raftpb/raft.proto:105 "The voters in the outgoing config." -> outgoing voters are part of the snapshot's configuration
\* evidence: history e515a6751 (raft: fix restoring joint configurations) "the joint configuration and was simply dropping it on the floor." -> installing a snapshot adopts its full joint configuration
\* evidence: impl source/raft.go:1404 "cs.Voters,"
\* watch:    raft.go:restore (membership pre-check); raft.go:handleSnapshot; confchange/restore.go:Restore; log.go:restore
\* verified: V02
\* note:     inferred: the pre-check's stated purpose is to drop snapshots only when the recipient is "not in the config", and outgoing voters are part of the ConfState; no test covers an outgoing-only recipient. The pre-check at raft.go:1403-1406 scans only cs.Voters and cs.Learners, so this revision appears not to satisfy the property (out/concerns.md).
\* clause install and adopt the full (joint) configuration: requirement — raft.go:1398-1400, raft.proto:105, e515a6751 (two-step reading, see note)
\* clause afterCommit=snapshotIndex: impl-abstraction — raft.go:1431 and log.go:301 only; no doc says the commit index jumps to the snapshot index
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   narrowed the intent's "taking its index as commit" to a clause line (impl only) and stated what each line supports; kept requirement on the two-step reading of raft.go:1398 plus raft.proto:105.
JointSnapshotMemberAcceptance == \A x\in history.restoreChecks:
    (x.fresh /\ x.follower /\ x.fullMember /\ ~x.matches) =>
       x.afterCommit=x.snapshotIndex /\ x.afterConfig=x.snapshotConfig
\* tracker/inflights.go:43-124: endpoints ordered, quota is not wire cardinality.
\* REQ-EVIDENCE QuotaIntegrity
\* intent:   The leader's uncommitted-size quota is non-negative and never exceeds the payload size of its unapplied log tail, and every peer's in-flight window holds at most MaxInflight indexes, added in order.
\* status:   mixed
\* evidence: comment source/raft.go:1597 "log tail but will never overestimate it. Saturate at 0 instead of" -> quota non-negative and never above the tail it tracks
\* evidence: history a370b6f6e (raft: fix bug in unbounded log growth prevention mechanism) "a fully committed Raft group could end up with a non-" -> an overestimating quota is a bug
\* evidence: comment source/tracker/progress.go:69 "entry should be added to inflights. The index MUST be added" -> in-flight indexes are added in order
\* evidence: comment source/tracker/inflights.go:53 "dispatched. Full() must be called prior to Add() to verify that there is room" -> at most MaxInflight entries in the window
\* evidence: test source/raft_flow_control_test.go:25 TestMsgAppFlowControlFull "2. when the window is full, no more msgApp can be sent." -> the window never exceeds MaxInflight
\* evidence: test source/raft_test.go:228 TestUncommittedEntryLimit "committed everything, but still tracking %d" -> the quota returns to zero once the tail is released
\* evidence: impl source/tracker/inflights.go:57 "cannot add into a Full inflights"
\* watch:    raft.go:increaseUncommittedSize; raft.go:reduceUncommittedSize; raft.go:becomeLeader; raft.go:advance; raft.go:reset; tracker/inflights.go:Add; tracker/inflights.go:FreeLE; tracker/inflights.go:FreeFirstOne; raft.go:maybeSendAppend
\* verified: V02
\* note:     the model bounds quota by the unapplied tail (applied+1..) because quota is released at Advance on CommittedEntries (raft.go:585), not at commit.
\* clause quota bounds and window size: requirement — raft.go:1597, a370b6f6e, inflights.go:53, raft_flow_control_test.go:25
\* clause strictly increasing in-flight indexes: impl-abstraction — inflights.go:53-55 asks for "a monotonic sequence" and progress.go:69-70 for "in order", not strict increase
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   narrowed "strictly increasing" in the intent to "added in order" (the sources ask only for a monotonic sequence) and recorded strictness as an impl-abstraction clause.
QuotaIntegrity == \A n\in Server:
    /\ raft[n].quota>=0
    /\ (raft[n].role="Leader" => raft[n].quota<=Weight(Suffix(Hist(raft[n]),raft[n].applied+1)))
    /\ \A p\in Members(raft[n]):
        /\ Len(raft[n].prs[p].inflight)<=MaxInflight
        /\ \A k\in 1..(Len(raft[n].prs[p].inflight)-1):
                raft[n].prs[p].inflight[k]<raft[n].prs[p].inflight[k+1]
\* Admission/rejection legality is checked in both directions, including acceptance.
ExpectedDecision(o) ==
    IF o.role="Leader" THEN
        IF ~o.member THEN "DropRemoved" ELSE IF o.transfer#0 THEN "DropTransfer"
        ELSE IF o.quota>0 /\ o.quota+o.weight>MaxUncommitted THEN "DropQuota" ELSE "Accepted"
    ELSE IF o.role#"Follower" \/ o.lead=0 THEN "DropNoLeader"
    ELSE IF ~o.forwarding THEN "DropForwardDisabled" ELSE "Forwarded"
\* REQ-EVIDENCE OutcomeSoundness
\* intent:   Every proposal handed to the core is dropped when the leader has a pending transfer or its quota is in use and would overflow, when the node is a candidate, or when forwarding is disabled; otherwise a leader accepts it and a follower forwards it.
\* status:   mixed
\* evidence: test source/raft_test.go:3558 TestLeaderTransferIgnoreProposal "should return drop proposal error while transferring" -> dropped during a pending transfer
\* evidence: comment source/raft.go:164 "limit is exceeded, proposals will begin to return ErrProposalDropped" -> dropped on quota overflow
\* evidence: comment source/raft.go:200 "DisableProposalForwarding set to true means that followers will drop" -> dropped when forwarding is disabled
\* evidence: doc source/doc.go:224 "When passed to candidate, 'MsgProp' is dropped." -> dropped by a candidate
\* evidence: test source/node_test.go:215 TestDisableProposalForwarding "proposals are not forwarded to" -> a follower forwards unless forwarding is disabled
\* evidence: impl source/raft.go:1018 "If we are not currently a member of the range (i.e. this node"
\* evidence: impl source/raft.go:1023 "if r.leadTransferee != None {"
\* watch:    raft.go:stepLeader (MsgProp); raft.go:stepCandidate (MsgProp); raft.go:stepFollower (MsgProp); raft.go:increaseUncommittedSize; node.go:run (propc)
\* verified: V02
\* note:     weight uses the model's RewriteConf, a mirror of raft.go:1028-1039. README.md:170 says there is no guarantee a proposal commits.
\* clause drops for transfer, quota, candidate and disabled forwarding; follower forwarding: requirement — evidence lines above
\* clause DropRemoved (leader no longer a member): unknown — only the narrating comment raft.go:1018-1020 ("drop any new proposals"); no doc or test
\* clause follower with no leader drops: impl-abstraction — raft.go:1290-1292 only
\* clause precedence order and "Accepted" as the default: impl-abstraction — raft.go:1013-1045 only
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement, unknown); handle clause by clause
\* review:   retyped the narrating raft.go:1018 comment to impl, so the removed-leader drop, no-leader drop, precedence and default acceptance move to clause lines; intent narrowed to the drop rules that keep non-impl evidence.
OutcomeSoundness == \A o\in history.outcomes:o.decision=ExpectedDecision(o)
\* Actual completed reads, not ReadState production. Prefix history is a symbolic SM.
\* REQ-EVIDENCE ReadBasis
\* intent:   Every completed read was served at an index confirmed by a quorum of the serving leader's configuration in its own term, after that leader committed an entry of its term (or as a singleton), and reflects every write completed before the read was invoked.
\* status:   mixed
\* evidence: doc source/README.md:28 "leader checks with quorum and bypasses Raft log before processing read-only queries" -> the read index is confirmed by a quorum
\* evidence: comment source/raft.go:49 "ReadOnlySafe guarantees the linearizability of the read only request by" -> quorum confirmation, and the read reflects earlier writes (linearizable)
\* evidence: test source/raft_test.go:2326 TestReadOnlyForNewLeader "ensures that a leader only accepts MsgReadIndex message" -> served only after the leader committed an entry of its term
\* evidence: comment source/node.go:182 "index, any linearizable read requests issued before the read request can be" -> the read reflects every write completed before it was invoked
\* evidence: impl source/raft.go:1051 "Reject read only request when this leader has not committed any log entry"
\* evidence: impl source/raft.go:1163 "if r.prs.Voters.VoteResult(r.readOnly.recvAck(m.From, m.Context)) != quorum.VoteWon {"
\* watch:    raft.go:stepLeader (MsgReadIndex, MsgHeartbeatResp); read_only.go:addRequest; read_only.go:recvAck; read_only.go:advance; raft.go:bcastHeartbeatWithCtx; tracker/tracker.go:IsSingleton
\* verified: V02
\* note:     confirmConfig, confirmAcks, confirmTerm and hist are ghosts attached by base.tla ReadRecord/ReleaseReadPrefix; ReadOnlyLeaseBased is not modeled. "Quorum" of a joint configuration means both majorities (quorum/joint.go:18).
\* clause JointWon(confirmConfig,confirmAcks), confirmTerm=term, committed entry of own term or singleton, beforeWrites covered: requirement — evidence lines above
\* clause leader\in VoterIDs(confirmConfig) and confirmConfig.voters#{}: unknown — impl only (raft.go:1163 counts r.prs.Voters); no source says a non-voter leader may not serve reads
\* clause confirmConfig equals ConfigOf(r.hist) or of an applied history covering it: model-internal — ties the ghost confirmation record to the model's configuration oracle
\* relabel:  requirement -> mixed (clause statuses: model-internal, requirement, unknown); handle clause by clause
\* review:   retyped the narrating raft.go:1051 comment to impl (the test carries that clause) and recorded the leader-membership and ghost configuration-matching conjuncts as clause lines.
ReadBasis == \A x\in history.readResults:
    LET r==x.rd IN
    /\ r.leader\in VoterIDs(r.confirmConfig)
    /\ r.confirmConfig.voters#{}
    /\ JointWon(r.confirmConfig,r.confirmAcks)
    /\ r.confirmConfig=ConfigOf(r.hist) \/
         \E c\in history.applied:r.confirmConfig=ConfigOf(c) /\ Covers(c,r.hist)
    /\ r.confirmTerm=r.term
    /\ r.singleton \/ (r.index>0 /\ r.hist[r.index].term=r.term)
    /\ \A h\in x.beforeWrites:Covers(Prefix(x.app,r.index),h)
\* REQ-EVIDENCE ReadApplication
\* intent:   A read completes only after the reader's applied history covers the read state's committed prefix and reaches its read index.
\* status:   requirement
\* evidence: comment source/node.go:64 "when its applied index is greater than the index in ReadState." -> a read is served only once the applied index passes the read index
\* evidence: comment source/rawnode.go:234 "Once the application advances further than the read" -> a read is served only once the application passes the read index
\* evidence: test source/raft_test.go:2207 TestReadOnlyOptionSafe "if rs.Index != tt.wri {" -> the read index is the leader's commit index, so reaching it covers the committed prefix
\* watch:    node.go:Ready (ReadStates); rawnode.go:ReadIndex; node.go:ReadIndex; raft.go:stepFollower (MsgReadIndexResp); read_only.go:ReadState
\* verified: V02
\* note:     the comments say "greater than" while this property (and the default ReadFence "Inclusive") use >=; see out/concerns.md. Read completion itself is a caller-model action (ProtocolCompleteRead), so there is no library impl line.
\* review:   ok
ReadApplication == \A x\in history.readResults:
    Covers(x.app,x.rd.hist) /\ Len(x.app)>=x.rd.index
\* REQ-EVIDENCE ReadCorrelation_Context
\* intent:   A completed read uses a read state whose request context equals the context of the request it completes.
\* status:   requirement
\* evidence: comment source/rawnode.go:236 "The read state will have the same rctx attached." -> the read state carries the request's context
\* evidence: comment source/read_only.go:21 "this state from ready, it's also caller's duty to differentiate if this" -> the caller matches read states to requests by context
\* evidence: test source/raft_test.go:2212 TestReadOnlyOptionSafe "requestCtx = %v, want %v" -> the read state's context equals the request's
\* evidence: impl source/raft.go:1171 "ReadState{Index: rs.index, RequestCtx: req.Entries[0].Data}"
\* watch:    read_only.go:addRequest; read_only.go:advance; raft.go:stepLeader (MsgReadIndex, MsgHeartbeatResp); raft.go:stepFollower (MsgReadIndexResp)
\* verified: V02
\* review:   ok
ReadCorrelation_Context == \A x\in history.readResults:
    x.rd.id=x.context
\* REQ-EVIDENCE ReadCorrelation_Ghost
\* intent:   The ghost request id carried by the read state is the completed request's id, and that request was actually handed to the core.
\* status:   model-internal
\* verified: V02
\* note:     rid and handoff are model bookkeeping (base.tla ReadRecord, ProtocolReadIndex, ProtocolCompleteRead), not library state.
\* review:   ok
ReadCorrelation_Ghost == \A x\in history.readResults:
    x.rd.rid=x.id /\ requests[x.id].handoff
\* REQ-EVIDENCE ReadCorrelation
\* intent:   conjunction of the parts below; kept so existing configs and references still work
\* status:   model-internal
\* verified: V02
\* note:     split by origin into ReadCorrelation_Context (requirement), ReadCorrelation_Ghost (model-internal)
\* review:   ok
ReadCorrelation == ReadCorrelation_Context /\ ReadCorrelation_Ghost
\* REQ-EVIDENCE NoUnexpectedFatal
\* intent:   No node ever reaches a state that the implementation treats as fatal (a panic path).
\* status:   mixed
\* evidence: comment source/raft.go:1441 "This should never happen. Either there's a bug in our config change" -> the snapshot-restore configuration panic should never happen (that path is not one of the model's Fatal reasons)
\* evidence: impl source/raft.go:704 "TODO(xiangli) remove the panic when the raft implementation is stable"
\* evidence: impl source/log.go:203 "Was the raft log corrupted, truncated, or lost?"
\* watch:    log.go:commitTo; log.go:appliedTo; log.go:append; log.go:maybeAppend; raft.go:becomeCandidate; raft.go:becomePreCandidate; raft.go:becomeLeader; raft.go:loadState; raft.go:applyConfChange; raft.go:maybeSendAppend; raft.go:Step (MsgHup slice); storage.go:Append; storage.go:CreateSnapshot
\* verified: V02
\* note:     the model's Fatal reasons (base.tla Fatal call sites) are library panics plus caller-contract violations; no workspace source states that the modeled panic paths are unreachable. raft.go:1388 ("This should never fire") guards a warning-and-return branch, not a panic, so it was dropped. raft.go:1477 says of the applyConfChange panic "TODO(tbg): return the error to the caller", i.e. an error, not an impossibility.
\* clause "conflict with committed entry", "append below committed": requirement in substance — implied by committed entries never changing (CommittedHistory, Raft-paper §5.4); no source states the panic itself is unreachable
\* clause role-transition, bounds, empty-proposal, Hup-slice, self-progress, snapshot and invalid-configuration panics: unknown — Panicf/panic code and TODOs only
\* clause "Storage.Append gap", "CreateSnapshot beyond lastIndex", "loadState commit out of range": model-internal — caller-contract violations that check the model's caller
\* relabel:  unknown -> mixed (clause statuses: model-internal, requirement, unknown); handle clause by clause
\* review:   status requirement -> unknown: raft.go:1441 covers an unmodeled restore path, raft.go:1388 is not a panic, and the raft.go:704 TODO states no rule; recorded per-reason clause lines.
NoUnexpectedFatal == \A n\in Server:raft[n].fatal=""

\* Structural assertions: do not disguise finite exploration limits as TypeOK.
\* REQ-EVIDENCE TypeOK
\* intent:   Model variables have the expected domains and value shapes.
\* status:   mixed
\* watch:    tracker/tracker.go:Config; confchange/confchange.go:checkInvariants
\* verified: V02
\* note:     structural typing of the model state; the two configuration clauses below duplicate parts of JointConfigurationShape, which carries their evidence. Not split: the mixed clauses sit inside one \A n quantifier body.
\* clause domains, role/term/vote/lead/commit/applied types, voter/learner subsets of Server, uoff>=1, progress mode, IsABag: model-internal — model representation only
\* clause learners\cap VoterIDs={}: requirement — tracker/tracker.go:37 "Invariant: Learners and Voters does not intersect"
\* clause learnersNext\subseteq outgoing: requirement — confchange/confchange.go:297-302 and raftpb/raft.proto:107-109
\* clause DOMAIN prs=Members: model-internal — mirrors the impl check confchange/confchange.go:290-293 ("no progress for %d")
\* relabel:  model-internal -> mixed (clause statuses: model-internal, requirement); handle clause by clause
\* review:   ok
TypeOK ==
    /\ DOMAIN raft=Server /\ DOMAIN disk=Server /\ DOMAIN ready=Server
    /\ DOMAIN application=Server /\ DOMAIN requests=RequestId
    /\ \A n\in Server:
       /\ raft[n].role\in {"Follower","PreCandidate","Candidate","Leader"}
       /\ raft[n].term\in Nat /\ raft[n].vote\in Server\cup {0}
       /\ raft[n].lead\in Server\cup {0} /\ raft[n].commit\in Nat /\ raft[n].applied\in Nat
       /\ raft[n].config.voters\subseteq Server /\ raft[n].config.outgoing\subseteq Server
       /\ raft[n].config.learners\subseteq Server /\ raft[n].config.learnersNext\subseteq Server
       /\ raft[n].config.learners\cap VoterIDs(raft[n].config)={}
       /\ raft[n].config.learnersNext\subseteq raft[n].config.outgoing
       /\ DOMAIN raft[n].prs=Members(raft[n])
       /\ raft[n].uoff>=1
       /\ \A p\in Members(raft[n]):raft[n].prs[p].mode\in {"Probe","Replicate","Snapshot"}
    /\ IsABag(wire)
\* REQ-EVIDENCE LogStructure_CommitBounds
\* intent:   On every node the applied index never exceeds the commit index, which never exceeds the last log index.
\* status:   requirement
\* evidence: comment source/log.go:37 "Invariant: applied <= committed" -> applied never exceeds commit
\* evidence: comment source/log.go:32 "committed is the highest log position that is known to be in" -> commit is a log position, so it does not exceed the last log index
\* evidence: test source/log_test.go:451 TestCommitTo "commit out of range -> panic" -> committing beyond the last index is refused (panics)
\* evidence: impl source/log.go:203 "tocommit(%d) is out of range [lastIndex(%d)]."
\* watch:    log.go:commitTo; log.go:appliedTo; log.go:restore; log.go:maybeAppend; raft.go:loadState; raft.go:handleHeartbeat; bootstrap.go:Bootstrap
\* verified: V02
\* review:   ok
LogStructure_CommitBounds == \A n\in Server:
    /\ raft[n].applied<=raft[n].commit
    /\ raft[n].commit<=Last(raft[n])
\* REQ-EVIDENCE LogStructure_LogShape
\* intent:   Each entry of a node's ghost history sits at the position named by its index, and the unstable suffix ends within the log.
\* status:   model-internal
\* watch:    log_unstable.go:truncateAndAppend; log_unstable.go:stableTo
\* verified: V02
\* note:     well-formedness of the model's log encoding; it mirrors the code's representation comments (log_unstable.go:19, storage.go:82) but checks only the model.
\* review:   ok
LogStructure_LogShape == \A n\in Server:
    /\ \A k\in DOMAIN Hist(raft[n]):Hist(raft[n])[k].index=k
    /\ raft[n].uoff+Len(raft[n].unstable)<=Last(raft[n])+1
\* REQ-EVIDENCE LogStructure
\* intent:   conjunction of the parts below; kept so existing configs and references still work
\* status:   model-internal
\* verified: V02
\* note:     split by origin into LogStructure_CommitBounds (requirement), LogStructure_LogShape (model-internal)
\* review:   ok
LogStructure == LogStructure_CommitBounds /\ LogStructure_LogShape

\* Public reference actions: identical protocol relation, total observer update.
Tick(n,timeout) == ProtocolTick(n,timeout) /\ quality'=QualityEvent("Tick",[node |-> n])
Campaign(n,timeout) == ProtocolCampaign(n,timeout) /\ quality'=QualityEvent("Campaign",[node |-> n])
TickQuiesced(n) == ProtocolTickQuiesced(n) /\ quality'=QualityEvent("TickQuiesced",[unused |-> 0])
TransferLeader(n,target,timeout) == ProtocolTransferLeader(n,target,timeout) /\ quality'=QualityEvent("TransferLeader",[node |-> n,target |-> target])
Invoke(n,id,kind,target,w,z,parent,ctx) == ProtocolInvoke(n,id,kind,target,w,z,parent,ctx) /\ quality'=QualityEvent("Invoke",[unused |-> 0])
InvokeV2(n,id,changes,transition,w,z,parent) ==
    ProtocolInvokeV2(n,id,changes,transition,w,z,parent) /\ quality'=QualityEvent("InvokeV2",[unused |-> 0])
Propose(n,id,timeout) == ProtocolPropose(n,id,timeout) /\ quality'=QualityEvent("Propose",[node |-> n,id |-> id])
ReadIndex(n,id,timeout) == ProtocolReadIndex(n,id,timeout) /\ quality'=QualityEvent("ReadIndex",[node |-> n,id |-> id])
ReturnAPI(id) == ProtocolReturnAPI(id) /\ quality'=QualityEvent("ReturnAPI",[unused |-> 0])
Cancel(id) == ProtocolCancel(id) /\ quality'=QualityEvent("Cancel",[unused |-> 0])
Receive(m,timeout) == ProtocolReceive(m,timeout) /\ quality'=QualityEvent("Receive",[message |-> m])
Lose(m) == ProtocolLose(m) /\ quality'=QualityEvent("Lose",[unused |-> 0])
Duplicate(m) == ProtocolDuplicate(m) /\ quality'=QualityEvent("Duplicate",[unused |-> 0])
ReportSnapshot(n,m,failed,timeout) == ProtocolReportSnapshot(n,m,failed,timeout) /\ quality'=QualityEvent("ReportSnapshot",[unused |-> 0])
ReportUnreachable(n,m,timeout) == ProtocolReportUnreachable(n,m,timeout) /\ quality'=QualityEvent("ReportUnreachable",[unused |-> 0])
Ready(n) == ProtocolReady(n) /\ quality'=QualityEvent("Ready",[unused |-> 0])
StartPersist(n,part) == ProtocolStartPersist(n,part) /\ quality'=QualityEvent("StartPersist",[unused |-> 0])
CompletePersist(n,part) == ProtocolCompletePersist(n,part) /\ quality'=QualityEvent("CompletePersist",[unused |-> 0])
StorageApplySnapshot(n) == ProtocolStorageApplySnapshot(n) /\ quality'=QualityEvent("StorageApplySnapshot",[unused |-> 0])
StorageAppend(n) == ProtocolStorageAppend(n) /\ quality'=QualityEvent("StorageAppend",[unused |-> 0])
StorageSetHardState(n) == ProtocolStorageSetHardState(n) /\ quality'=QualityEvent("StorageSetHardState",[unused |-> 0])
Publish(n) == ProtocolPublish(n) /\ quality'=QualityEvent("Publish",[unused |-> 0])
QueueApplication(n) == ProtocolQueueApplication(n) /\ quality'=QualityEvent("QueueApplication",[unused |-> 0])
Advance(n) == ProtocolAdvance(n) /\ quality'=QualityEvent("Advance",[unused |-> 0])
ApplySnapshot(n) == ProtocolApplySnapshot(n) /\ quality'=QualityEvent("ApplySnapshot",[unused |-> 0])
ApplyEntry(n,timeout) == ProtocolApplyEntry(n,timeout) /\ quality'=QualityEvent("ApplyEntry",[node |-> n])
FinishApplication(n) == ProtocolFinishApplication(n) /\ quality'=QualityEvent("FinishApplication",[unused |-> 0])
SaveApplication(n) == ProtocolSaveApplication(n) /\ quality'=QualityEvent("SaveApplication",[unused |-> 0])
CompleteWrite(n,id) == ProtocolCompleteWrite(n,id) /\ quality'=QualityEvent("CompleteWrite",[unused |-> 0])
CompleteRead(n,id,k) == ProtocolCompleteRead(n,id,k) /\ quality'=QualityEvent("CompleteRead",[unused |-> 0])
CreateSnapshot(n,k) == ProtocolCreateSnapshot(n,k) /\ quality'=QualityEvent("CreateSnapshot",[unused |-> 0])
PersistLocalSnapshot(n) == ProtocolPersistLocalSnapshot(n) /\ quality'=QualityEvent("PersistLocalSnapshot",[unused |-> 0])
Compact(n,k) == ProtocolCompact(n,k) /\ quality'=QualityEvent("Compact",[unused |-> 0])
SnapshotAvailability(n,available) == ProtocolSnapshotAvailability(n,available) /\ quality'=QualityEvent("SnapshotAvailability",[unused |-> 0])
Crash(n) == ProtocolCrash(n) /\ quality'=QualityEvent("Crash",[unused |-> 0])
Stop(n) == ProtocolStop(n) /\ quality'=QualityEvent("Stop",[unused |-> 0])
Restart(n,timeout) == ProtocolRestart(n,timeout) /\ quality'=QualityEvent("Restart",[unused |-> 0])

Timeouts == ElectionTick..(2*ElectionTick-1)
SingleChangeBatches == {<<Change(k,n)>>:k\in LegacyConfKinds,n\in Server}
ReplacementBatches == {<<Change("Remove",a),Change("AddVoter",b)>>:a,b\in Server}
V2Batches == {<<>>}\cup SingleChangeBatches\cup ReplacementBatches
ClientActions ==
    \/ \E n\in Server,id\in RequestId,kind\in Kinds\cup {"Read"},
          target\in Server\cup {0},w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup {0}:
          \E ctx\in {id,0}: Invoke(n,id,kind,target,w,z,parent,ctx)
    \/ \E n\in Server,id\in RequestId,changes\in V2Batches,
          transition\in {"Auto","JointImplicit","JointExplicit"},
          w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup {0}:
          InvokeV2(n,id,changes,transition,w,z,parent)
ReactiveActions ==
    \/ \E n\in Server,id\in RequestId,t\in Timeouts:Propose(n,id,t)
    \/ \E n\in Server,id\in RequestId,t\in Timeouts:ReadIndex(n,id,t)
    \/ \E id\in RequestId:ReturnAPI(id)
    \/ \E m\in DOMAIN wire,t\in Timeouts:Receive(m,t)
    \/ \E n\in Server:Ready(n) \/ Publish(n) \/ QueueApplication(n) \/ Advance(n)
             \/ StorageApplySnapshot(n) \/ StorageAppend(n) \/ StorageSetHardState(n)
             \/ ApplySnapshot(n) \/ FinishApplication(n) \/ SaveApplication(n)
             \/ PersistLocalSnapshot(n)
    \/ \E n\in Server,part\in {"All","Entries","HS","Snapshot"}:StartPersist(n,part) \/ CompletePersist(n,part)
    \/ \E n\in Server,t\in Timeouts:ApplyEntry(n,t) \/ Restart(n,t)
    \/ \E n\in Server,id\in RequestId:CompleteWrite(n,id) \/
             (\E k\in DOMAIN application[n].reads:CompleteRead(n,id,k))
Next ==
    \/ ReactiveActions
    \/ ClientActions
    \/ \E n\in Server,t\in Timeouts:Tick(n,t) \/ Campaign(n,t) \/
                           (\E p\in Server:TransferLeader(n,p,t))
    \/ \E n\in Server:Crash(n) \/ Stop(n) \/ TickQuiesced(n) \/
         (\E k\in 1..Last(raft[n]):CreateSnapshot(n,k) \/ Compact(n,k)) \/
         SnapshotAvailability(n,TRUE) \/ SnapshotAvailability(n,FALSE)
    \/ \E id\in RequestId:Cancel(id)
    \/ \E m\in DOMAIN wire:Lose(m) \/ Duplicate(m)
    \/ \E m\in history.sent,t\in Timeouts:
         ReportUnreachable(m.from,m,t) \/
         (\E failed\in BOOLEAN:ReportSnapshot(m.from,m,failed,t))
Spec == Init /\ [][Next]_vars
=============================================================================
