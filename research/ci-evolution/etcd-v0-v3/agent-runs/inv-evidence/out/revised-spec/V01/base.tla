------------------------------- MODULE base -------------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, Bags, TLC

(***************************************************************************
Category A. etcd-raft incremental revision 16c5274b589aa75c634a1a5f2b05cf66aaf37dcc.
Source references are relative to ../../source. S1..S6 are retained V00
scenarios; U1..U5 are the incremental scenarios in modeling-brief.md.
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
    \* raft.go:numOfPendingConf recognizes only EntryConfChange in this revision.
    \* Retain the implementation omission for EntryConfChangeV2.
    ELSE IF \E k \in (r.applied+1)..r.commit: Hist(r)[k].kind\in LegacyConfKinds THEN r
    ELSE IF r.preVote THEN CampaignPreElection(r,timeout)
         ELSE CampaignElection(r,FALSE,timeout)

\* raft.go:885-920. Removed nonlearners may grant; candidate membership not tested.
StepVote(r,m) ==
    IF r.id\in r.config.learners THEN r ELSE
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
\* raft.go:1361-1430. Revision 16c5274 checks and rebuilds only ConfState.Nodes
\* and Learners, dropping NodesJoint/LearnersNext/AutoLeave. Keep that behavior
\* source-faithful so JointSnapshotRecovery can detect the resulting loss.
RestoreProjection(cfg) ==
    [EmptyConfig EXCEPT !.voters=cfg.voters, !.learners=cfg.learners]
Restore(r,s,timeout) ==
    IF s.index<=r.commit THEN r
    ELSE IF r.role#"Follower" THEN BecomeFollower(r,r.term+1,0,timeout)
    ELSE IF r.id\notin s.config.voters\cup s.config.learners THEN r
    ELSE IF Matches(r,s.index,s.term) THEN CommitTo(r,s.index)
    ELSE LET cfg==RestoreProjection(s.config) IN
         [r EXCEPT !.commit=s.index, !.usnap=s, !.unstable= <<>>, !.uoff=s.index+1,
           !.config=cfg, !.cfgHist=s.hist,
           !.yes={}, !.no={},
           !.prs=[n \in cfg.voters\cup cfg.learners |->
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
\* raftpb/confchange.go: LeaveJoint requires zero Transition as well as no changes.
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
    commitUses |-> {}, snapshots |-> {}, autoLeaveChecks |-> {},
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
\* raft.go:789-920; lease suppression precedes learner filtering and term reset.
\* Removed nonlearners and candidates outside the voter set are NOT excluded.
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
        grant==~lease /\ ~stale /\ ~o.learner /\ fresh /\ can
        silence==lease \/ (stale /\ m.type="MsgVote") \/ (~stale /\ o.learner)
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
VoteDecisionEligibility == \A o\in quality.votes:VoteContract(o)
CampaignDecisionEligibility == \A o\in quality.campaigns:CampaignContract(o)
TransferDecisionEligibility == \A o\in quality.transfers:TransferContract(o)
RequestCorrelatedConfigurationEffects == \A o\in quality.effects:EffectContract(o)
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
       IN SetCore(m.to,a,"Receive")
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

\* node.go:573-604 / log.go:151-160: clamped, encoded-size-limited Ready page.
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
       \* rawnode.go:122-150; RawNode.Ready is read-only. node.go:308-320,
       \* 386-388 accepts only after the Ready is actually delivered.
       /\ raft'=[raft EXCEPT ![n]=[r EXCEPT
            !.out=IF n\in RawNodes THEN @ ELSE EmptyBag,
            !.readySeq=b.id,
            !.readStates=IF n\in RawNodes THEN @ ELSE <<>>,
            !.prevSS=IF n\in RawNodes THEN @ ELSE b.ss]]
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
\* rawnode.go:139-191, raft.go:554-592 and log_unstable.go:77-114.
\* RawNode accepts (clears messages/read states) at Advance; Node accepted when
\* Ready was sent. Auto-leave is appended after the applied cursor advances.
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
        !.out=IF n\in RawNodes THEN EmptyBag ELSE @,
        !.quota=Max(0,@-Weight(b.committed)),
        !.unstable=IF stable THEN Suffix(@,last.index+2-r.uoff) ELSE @,
        !.uoff=IF stable THEN last.index+1 ELSE @,
        !.usnap=IF b.snapshot.index>0 /\ r.usnap.index=b.snapshot.index THEN EmptySnapshot ELSE @,
        !.prevHS=b.hs,
        !.prevSS=IF n\in RawNodes THEN b.ss ELSE @,
        !.readStates=IF n\in RawNodes THEN <<>> ELSE @]
ProtocolAdvance(n) ==
    /\ Live(n) /\ ready[n].active /\ Persisted(ready[n])
    /\ ready[n].installed=Parts(ready[n]) /\ ready[n].published /\ ready[n].queued
    /\ EarlyAdvance \/ application[n].jobs= <<>>
    /\ LET r==raft[n] b==ready[n] a==AdvanceCore(r,b,n) IN
       /\ raft'=[raft EXCEPT ![n]=a]
       /\ history'=Observe([history EXCEPT !.lostReads=@\cup
            (IF n\in RawNodes /\ b.reads# <<>> THEN SeqSet(r.readStates)\SeqSet(application[n].reads) ELSE {}),
            !.acks=@\cup
            {[before |-> Hist(r), after |-> Hist(a), oldSnap |-> r.usnap.index,
              batchSnap |-> b.snapshot.index, afterSnap |-> a.usnap.index,
              cursor |-> b.cursor, applied |-> a.applied]},
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
\* raft.go:321-382, rawnode.go:40-58. Construction loads stable term/vote but,
\* in this revision, only the incoming Nodes and Learners ConfState fields.
RestartCore(n,timeout) ==
    LET d==disk[n] h==DiskHist(d)
        app==IF RecoveryMode="AppliedAdapter" THEN d.savedApp ELSE d.snapshot.hist
        fullCfg==IF RecoveryMode="AppliedAdapter" THEN ConfigOf(app) ELSE d.snapshot.config
        cfg==RestoreProjection(fullCfg)
        baseR==[InitialRaft(n,timeout) EXCEPT !.incarnation=raft[n].incarnation+1,
          !.term=d.hs.term, !.vote=d.hs.vote, !.config=cfg, !.cfgHist=app,
          !.store=Store(h,d.snapshot,d.snapshot.index,d.hs), !.unstable= <<>>,
          !.uoff=Len(h)+1, !.commit=d.snapshot.index, !.applied=d.snapshot.index,
          !.prs=[p\in cfg.voters\cup cfg.learners |-> Progress(0,1,FALSE)]]
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
ElectionSafety == \A a,b\in history.wins:a.term=b.term => a.node=b.node
LogMatching == \A n,p\in Server:
    \A k\in 1..Min(Last(raft[n]),Last(raft[p])):
       (Hist(raft[n])[k].term=Hist(raft[p])[k].term /\ Hist(raft[n])[k].term>0)
          => Prefix(Hist(raft[n]),k)=Prefix(Hist(raft[p]),k)
LeaderCompleteness == \A w\in history.wins:\A c\in history.obligations:
                         w.term>c.term => Covers(w.hist,c.hist)
CommittedHistory == /\ history.liveOK
    /\ \A a,b\in history.obligations:Compatible(a.hist,b.hist)
    /\ \A n\in Server:\A c\in history.obligations:
         raft[n].alive => Compatible(Prefix(Hist(raft[n]),raft[n].commit),c.hist)
AppliedAgreement == \A a,b\in history.applied:Compatible(a,b)
\* Durable term/vote promises survive constructor; no equality to volatile votes.
VoteRecovery == \A x\in history.recovery:
    x.term>=x.savedTerm /\ (x.term=x.savedTerm /\ x.savedVote#0 => x.vote=x.savedVote)
RecoveryBacking == \A x\in history.recovery:
    /\ x.commit<=Len(x.diskHist)
    /\ \A k\in 1..x.commit:x.diskHist[k].kind#"Missing"
    /\ Covers(x.diskHist,x.app)
PromiseBacking == \A p\in history.promises:p.backed
\* README.md:120,193. Configuration has a committed/constructor/snapshot origin.
ConfigurationOrigin == \A n\in Server:
    raft[n].alive =>
       /\ raft[n].config=ConfigOf(raft[n].cfgHist)
       /\ Covers(Hist(raft[n]),raft[n].cfgHist)
       /\ Len(raft[n].cfgHist)<=raft[n].commit
\* Each configuration entry must commit using its predecessor voter configuration.
\* Bootstrap entries (id=0) are explicit constructor axioms, not quorum decisions.
ConfigurationTransitionSafety == \A c\in history.commitUses:
    \A k\in (c.oldCommit+1)..Len(c.hist):
       (c.hist[k].kind\in ConfKinds /\ c.hist[k].id#0) =>
             c.config=ConfigOf(Prefix(c.hist,k-1))
LearnerEligibility == /\ \A x\in history.grants:~x.learner
                      /\ \A x\in history.campaigns:~x.learner
QuorumAccounting ==
    /\ \A w\in history.wins:w.config.voters#{} /\ JointWon(w.config,w.yes)
    /\ \A c\in history.commitUses:c.config.voters#{} /\
         c.matches\subseteq VoterIDs(c.config) /\ JointWon(c.config,c.matches)
\* raft.go:613 versus 1039-1091: distinguish self's volatile evidence.
ReplicationEvidence == \A n\in Server:
    raft[n].alive /\ raft[n].role="Leader" =>
      \A p\in Members(raft[n])\{n}:
       LET pr==raft[n].prs[p] IN
       pr.match>0 => /\ Len(pr.evidence)>=pr.match
                    /\ Covers(Hist(raft[n]),Prefix(pr.evidence,pr.match))
SnapshotValid(s) == s.index=Len(s.hist) /\ s.config=ConfigOf(s.hist) /\
                    (s.index>0 => s.hist[s.index].term=s.term)
SnapshotBacking ==
    /\ \A s\in history.snapshots:SnapshotValid(s)
    /\ \A n\in Server:SnapshotValid(raft[n].usnap) /\ SnapshotValid(disk[n].snapshot)
AckPreservation == \A a\in history.acks:
    /\ \/ a.before=a.after
       \/ /\ Len(a.after)=Len(a.before)+1 /\ Prefix(a.after,Len(a.before))=a.before
          /\ LET e==a.after[Len(a.after)] IN e.kind="V2" /\ e.changes= <<>>
    /\ (a.oldSnap#0 /\ a.oldSnap#a.batchSnap => a.afterSnap=a.oldSnap)
    /\ (a.cursor#0 => a.applied=a.cursor)
ReadyAccounting ==
    /\ history.lostReads={}
    /\ \A b\in history.readyChecks:
        /\ b.cursor<=b.commit
        /\ IF b.entries= <<>> THEN b.cursor=b.snapshot ELSE
             /\ Head(b.entries).index=Max(b.from+1,b.first)
             /\ b.cursor=b.entries[Len(b.entries)].index
             /\ \A k\in DOMAIN b.entries:b.entries[k].index=Head(b.entries).index+k-1
\* rawnode.go:122-150: Ready itself does not accept RawNode state; Node does.
ReadyOwnership == \A b\in history.readyChecks:
    /\ b.quotaAfter=b.quotaBefore
    /\ IF b.raw THEN b.outAfter=b.outBefore /\ b.readsAfter=b.readsBefore
       ELSE b.outAfter=EmptyBag /\ b.readsAfter= <<>>
\* raft.go:554-581: every eligible Advance appends leave-joint or records the
\* quota-retry cursor. This checks the effect, not eventual scheduling.
AutoLeaveAdvance == \A a\in history.autoLeaveChecks:
    a.eligible =>
      \/ /\ Len(a.afterHist)=a.beforeLast+1
         /\ a.afterHist[Len(a.afterHist)].kind="V2"
         /\ a.afterHist[Len(a.afterHist)].changes= <<>>
      \/ /\ a.decision="DropQuota" /\ a.pending=Len(a.afterHist)
\* tracker.Config shape and the source's persisted ConfState must survive a load.
JointConfigurationShape == \A n\in Server:
    LET c==raft[n].config IN
    \/ c=EmptyConfig
    \/ /\ c.voters#{}
       /\ c.learners\cap VoterIDs(c)={}
       /\ c.learnersNext\subseteq c.outgoing
       /\ c.learnersNext\cap (c.voters\cup c.learners)={}
       /\ (c.outgoing={} => c.learnersNext={} /\ ~c.autoLeave)
JointSnapshotRecovery ==
    /\ \A x\in history.recovery:
         x.expectedConfig.outgoing#{} => x.config=x.expectedConfig
    /\ \A n\in Server:
         raft[n].alive /\ ConfigOf(raft[n].cfgHist).outgoing#{} =>
             raft[n].config=ConfigOf(raft[n].cfgHist)
\* tracker/inflights.go:43-124: endpoints ordered, quota is not wire cardinality.
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
OutcomeSoundness == \A o\in history.outcomes:o.decision=ExpectedDecision(o)
\* Actual completed reads, not ReadState production. Prefix history is a symbolic SM.
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
ReadApplication == \A x\in history.readResults:
    Covers(x.app,x.rd.hist) /\ Len(x.app)>=x.rd.index
ReadCorrelation == \A x\in history.readResults:
    x.rd.id=x.context /\ x.rd.rid=x.id /\ requests[x.id].handoff
NoUnexpectedFatal == \A n\in Server:raft[n].fatal=""

\* Structural assertions: do not disguise finite exploration limits as TypeOK.
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
LogStructure == \A n\in Server:
    /\ raft[n].applied<=raft[n].commit
    /\ raft[n].commit<=Last(raft[n])
    /\ \A k\in DOMAIN Hist(raft[n]):Hist(raft[n])[k].index=k
    /\ raft[n].uoff+Len(raft[n].unstable)<=Last(raft[n])+1

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
