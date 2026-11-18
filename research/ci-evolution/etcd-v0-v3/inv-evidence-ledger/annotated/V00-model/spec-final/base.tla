------------------------------- MODULE base -------------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, Bags, TLC

(***************************************************************************
Category A. etcd-raft V00 d58d5d159ae1a1f644a10003f2d8b3b807cd0b3a.
Source references are relative to ../../source. S1..S6 denote brief scenarios.
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
EmptyConfig == [voters |-> {}, learners |-> {}]
BootConfig == [voters |-> Server \ Joining, learners |-> {}]
EmptySnapshot == [index |-> 0, term |-> 0, hist |-> <<>>, config |-> EmptyConfig]
Entry(t,i,k,id,target,w,z) ==
    [term |-> t, index |-> i, kind |-> k, id |-> id, target |-> target,
     weight |-> w, encoded |-> z]
\* Default abstract weights; Trace overrides these with measured protobuf sizes.
BootstrapPayload == 1
BootstrapEncoded == 1
EmptyEncoded == 1
BootLog == [k \in 1..Len(BootPeers) |-> Entry(1,k,"AddVoter",0,BootPeers[k],BootstrapPayload,BootstrapEncoded)]
ConfKinds == {"AddVoter","AddLearner","Remove","Update"}
Kinds == ConfKinds \cup {"Normal"}
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
Members(r) == r.config.voters \cup r.config.learners
Promotable(r) == r.id \in r.config.voters
\* quorum/majority.go:170-201 includes empty-set win and even-sized loss.
Won(voters,yes) == voters={} \/ Cardinality(voters \cap yes)>Cardinality(voters)\div 2
Lost(voters,yes,no) == ~Won(voters,yes) /\
    Cardinality(voters \ no)<=Cardinality(voters)\div 2
QuorumIndex(r) == IF r.config.voters={} THEN Last(r)+1 ELSE
    MaxSet({i \in 0..Last(r): Won(r.config.voters,
                          {n \in r.config.voters:r.prs[n].match>=i})})
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
          {[hist |-> Prefix(Hist(r),i), voters |-> r.config.voters,
            term |-> r.term, oldCommit |-> r.commit,
            matches |-> {n\in r.config.voters:r.prs[n].match>=i}]}] ELSE r
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
AppendEntry(r,es) == LET fixed==[k \in DOMAIN es |->
                                     [es[k] EXCEPT !.term=r.term, !.index=Last(r)+k]] IN
    IF r.quota>0 /\ r.quota+Weight(es)>MaxUncommitted
    THEN [r EXCEPT !.decision="DropQuota"]
    ELSE LET a==AppendLog([r EXCEPT !.quota=@+Weight(es)],fixed)
             b==[a EXCEPT !.prs[r.id]=MaybeUpdate(@,Last(a),Hist(a))]
         IN MaybeCommit(b)
\* raft.go:693-726. Record the actual election before reset; check it separately.
BecomeLeader(r,timeout) ==
    IF r.role="Follower" THEN Fatal(r,"follower to leader")
    ELSE IF r.id \notin DOMAIN r.prs THEN Fatal(r,"leader missing self progress")
    ELSE LET win==[node |-> r.id, term |-> r.term, hist |-> Hist(r),
                   voters |-> r.config.voters, yes |-> r.yes]
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
\* raft.go:729-770; campaign warning is deliberately not a promotability guard.
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
    IN IF Won(a.config.voters,a.yes) THEN BecomeLeader(a,timeout)
       ELSE BroadcastVotes(a,a.config.voters\{a.id},FALSE,forced)
CampaignPreElection(r,timeout) ==
    IF r.role="Leader" THEN Fatal(r,"leader to pre-candidate") ELSE
    LET a==[r EXCEPT !.role="PreCandidate", !.lead=0, !.yes={r.id}, !.no={},
             !.campaigns=@ \cup {[node |-> r.id, learner |-> r.id\in r.config.learners]}]
    IN IF Won(a.config.voters,a.yes) THEN CampaignElection(a,FALSE,timeout)
       ELSE BroadcastVotes(a,a.config.voters\{a.id},TRUE,FALSE)
\* raft.go:859-883 and log.go:347-359. Do not clamp the Hup scan to First.
StepHup(r,timeout) ==
    IF r.role="Leader" \/ ~Promotable(r) THEN r
    ELSE IF r.applied+1<First(r) THEN Fatal(r,"Hup unapplied slice compacted")
    ELSE IF \E k \in (r.applied+1)..r.commit: Hist(r)[k].kind\in ConfKinds THEN r
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
\* raft.go:1327-1393. Full restore is one atomic core operation, not application.
Restore(r,s,timeout) ==
    IF s.index<=r.commit THEN r
    ELSE IF r.role#"Follower" THEN BecomeFollower(r,r.term+1,0,timeout)
    ELSE IF r.id\notin s.config.voters\cup s.config.learners THEN r
    ELSE IF Matches(r,s.index,s.term) THEN CommitTo(r,s.index)
    ELSE [r EXCEPT !.commit=s.index, !.usnap=s, !.unstable= <<>>, !.uoff=s.index+1,
           !.config=s.config, !.cfgHist=s.hist,
           !.yes={}, !.no={},
           !.prs=[n \in s.config.voters\cup s.config.learners |->
                     Progress(IF n=r.id THEN s.index ELSE 0,s.index+1,TRUE)]]
HandleSnapshot(r,m,timeout) == LET a==Restore(r,m.snapshot,timeout) IN
    Send(a,[Message("MsgAppResp",r.id,m.from,a.term) EXCEPT
            !.index=IF a.usnap=m.snapshot /\ m.snapshot.index>r.commit THEN Last(a) ELSE a.commit,
            !.witness=Prefix(Hist(a),a.commit)])

\* raft.go:977-988; entry rewriting and pending bookkeeping precede quota check.
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
\* raft.go:995-1026, read_only.go:56-75. Context id 0 denotes empty bytes.
ReadRecord(r,m) == [EmptyRead EXCEPT !.id=m.context, !.rid=m.request, !.requester=m.from,
    !.index=r.commit, !.term=r.term, !.leader=r.id, !.config=r.config,
    !.acks={r.id}, !.hist=Prefix(Hist(r),r.commit)]
DeliverReadState(r,rd) == IF rd.requester\in {0,r.id}
    THEN [r EXCEPT !.readStates=Append(@,rd)]
    ELSE Send(r,[Message("MsgReadIndexResp",r.id,rd.requester,r.term) EXCEPT
          !.index=rd.index, !.context=rd.id, !.request=rd.id, !.read=rd])
StepLeaderReadIndex(r,m) ==
    IF Cardinality(r.config.voters)=1 THEN
        DeliverReadState(r,[ReadRecord(r,m) EXCEPT !.singleton=TRUE,
            !.confirmConfig=r.config, !.confirmAcks={r.id}, !.confirmTerm=r.term])
    ELSE IF Term(r,r.commit)#r.term THEN r
    ELSE LET exists==\E k \in DOMAIN r.readQueue:r.readQueue[k].id=m.context
             a==IF exists THEN r ELSE [r EXCEPT !.readQueue=Append(@,ReadRecord(r,m))]
         IN BcastHeartbeat(a,m.context)
\* raft.go:1105-1120; a later context releases an entire prefix under CURRENT voters.
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
    IN IF ~Won(a.config.voters,acks) THEN a ELSE
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
\* raft.go:940-961; recently added nodes retain their source-defined activity grace.
StepCheckQuorum(r,timeout) ==
    LET a==IF r.id\in Members(r) THEN [r EXCEPT !.prs[r.id].active=TRUE] ELSE r
        active=={n \in a.config.voters:a.prs[n].active}
        b==IF Won(a.config.voters,active) THEN a ELSE BecomeFollower(a,a.term,0,timeout)
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
         IN IF Won(a.config.voters,a.yes) THEN
                IF a.role="PreCandidate" THEN CampaignElection(a,FALSE,timeout)
                ELSE BcastAppend(BecomeLeader(a,timeout))
            ELSE IF Lost(a.config.voters,a.yes,a.no) THEN BecomeFollower(a,a.term,0,timeout)
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

\* raft.go:1403-1452. Cancellation is deterministic over entry identity.
ConfigAfter(cfg,e) ==
    IF e.kind\notin ConfKinds \/ e.target=0 \/ e.id\in CancelChanges THEN cfg ELSE
    CASE e.kind="AddVoter" -> [cfg EXCEPT !.voters=@\cup {e.target}, !.learners=@\{e.target}]
      [] e.kind="AddLearner" -> IF e.target\in cfg.voters THEN cfg
                                ELSE [cfg EXCEPT !.learners=@\cup {e.target}]
      [] e.kind="Remove" -> [cfg EXCEPT !.voters=@\{e.target}, !.learners=@\{e.target}]
      [] OTHER -> cfg
RECURSIVE ConfigOf(_)
ConfigOf(h) == IF h= <<>> THEN EmptyConfig ELSE ConfigAfter(ConfigOf(Prefix(h,Len(h)-1)),h[Len(h)])
ApplyConfCore(r,e,timeout) ==
    LET canceled==e.target=0 \/ e.id\in CancelChanges \/
                    (CancelUnknownRemovals /\ e.kind="Remove" /\ e.target\notin Members(r))
        cfg==ConfigAfter(r.config,e)
        members==cfg.voters\cup cfg.learners
        changed==cfg#r.config
        a==IF ~canceled /\ e.kind="Remove" /\ e.target\notin Members(r)
           THEN Fatal(r,"remove unknown peer") ELSE
           [r EXCEPT !.config=cfg, !.prs=[n \in members |->
              IF n\notin Members(r) THEN Progress(0,Last(r)+1,TRUE)
              ELSE IF changed /\ n=e.target /\ e.kind\in {"AddVoter","AddLearner"}
                   THEN [r.prs[n] EXCEPT !.active=TRUE] ELSE r.prs[n]]]
    IN IF a.fatal#"" \/ r.role#"Leader" \/ r.id\notin cfg.voters \/ cfg.voters={} THEN a ELSE
       LET b==IF ~canceled /\ e.kind="Remove" THEN MaybeCommit(a) ELSE a
           c==IF b.commit>a.commit THEN BcastAppend(b) ELSE b
       IN IF c.transfer#0 /\ c.transfer\notin members THEN [c EXCEPT !.transfer=0] ELSE c

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
    weight |-> 0, encoded |-> 1, parent |-> 0, handoff |-> FALSE,
    core |-> "", result |-> "", context |-> 0, beforeWrites |-> {}, completed |-> FALSE]
EmptyHistory == [wins |-> {}, grants |-> {}, campaigns |-> {}, obligations |-> {},
    promises |-> {}, applied |-> {}, writes |-> {}, readResults |-> {},
    acks |-> {}, readyChecks |-> {}, recovery |-> {}, outcomes |-> {},
    commitUses |-> {}, snapshots |-> {}, liveOK |-> TRUE, sent |-> {}, lostReads |-> {}, events |-> {}]

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
    [node |-> r.id, voters |-> r.config.voters, role |-> r.role, pre |-> r.preVote,
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
        singleton==Cardinality(o.voters)=1
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
    [node |-> r.id, target |-> target, voters |-> r.config.voters, learners |-> r.config.learners,
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
        cancel==e.target=0 \/ e.id\in CancelChanges
        voterAdd==~cancel /\ e.kind="AddVoter"
        learnerAdd==~cancel /\ e.kind="AddLearner" /\ e.target\notin b.voters
        remove==~cancel /\ e.kind="Remove"
        vs==IF voterAdd THEN b.voters\cup {e.target} ELSE IF remove THEN b.voters\{e.target} ELSE b.voters
        ls==IF voterAdd \/ remove THEN b.learners\{e.target} ELSE IF learnerAdd THEN b.learners\cup {e.target} ELSE b.learners
    IN /\ o.after=[voters |-> vs,learners |-> ls]
       /\ e.index\in DOMAIN o.committed /\ o.committed[e.index]=e
       /\ IF e.id=0 THEN e.kind="AddVoter" /\ e.term=1 /\ e.target\in SeqSet(BootPeers)
          ELSE e.id\in RequestId /\ q.handoff /\ q.kind=e.kind /\ q.target=e.target

ProposalObservation(r,es,a,qs) ==
    [node |-> r.id, role |-> r.role, voters |-> r.config.voters, learners |-> r.config.learners,
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
                 /\ (e.id#0 => e.id\in RequestId /\ o.requests[e.id].kind=e.kind /\ o.requests[e.id].target=e.target)
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
         LET q==requests[p.id] e==Entry(0,0,q.kind,p.id,q.target,q.weight,q.encoded) IN
         [EmptyQuality EXCEPT !.proposals={ProposalObservation(raft[p.node],<<e>>,raft'[p.node],requests)}]
      [] event="ApplyEntry" ->
         LET e==Head(Head(application[p.node].jobs).entries) IN
         IF e.kind\in ConfKinds THEN [EmptyQuality EXCEPT
            !.effects={EffectObservation(raft[p.node],e,raft'[p.node],requests)}] ELSE EmptyQuality
      [] OTHER -> EmptyQuality
\* REQ-EVIDENCE VoteDecisionEligibility
\* intent:   every observed MsgVote/MsgPreVote step obeys the documented vote rules: no term change or vote inside a leader lease, no answer from a learner, no term change for a PreVote, at most one vote per term and only for an up-to-date candidate, and a granted response carries the message's term.
\* status:   mixed
\* evidence: comment source/raft.go:794 "If a server receives a RequestVote request within the minimum election timeout" -> no term update and no vote inside a leader lease
\* evidence: comment source/raft.go:902 "When responding to Msg{Pre,}Vote messages we include the term" -> a granted response carries the message's term
\* evidence: comment source/raft.go:803 "Never change our term in response to a PreVote" -> no term change for a PreVote
\* evidence: test source/raft_paper_test.go:234 TestFollowerVote "each follower will vote for at most one" -> at most one vote per term
\* evidence: test source/raft_paper_test.go:820 TestVoter "the voter denies its vote if its own log is more up-to-date" -> vote only for an up-to-date candidate
\* evidence: test source/raft_test.go:1446 TestRecvMsgVote "testRecvMsgVote(t, pb.MsgVote)" -> grant/reject by up-to-date check and prior vote
\* evidence: comment source/raft.go:126 "It does not vote or promote itself." -> a learner does not vote
\* evidence: test source/raft_paper_test.go:77 TestRejectStaleTermMessage "Our implementation ignores the request instead." -> only clause stale-term below (records an implementation choice, not part of the intent)
\* evidence: impl source/raft.go:892 "We can vote if this is a repeat of a vote we've already cast..."
\* evidence: impl source/raft.go:893 "canVote := r.Vote == m.From ||"
\* watch:    raft.go:Step; raft.go:send; log.go:isUpToDate; raft.go:reset
\* verified: V00
\* note:     contract is a decision-time observer (quality.votes); removed non-learners and candidates outside the voter set are deliberately not excluded (base.tla VoteContract comment). Mixed origins, not splittable (one LET); per-clause status below. raft.go:892 is retyped to impl: it narrates the canVote expression line by line.
\* clause lease: requirement — comment raft.go:794-795 (do not update term or grant vote while in lease); the campaignTransfer bypass (m.forced) is impl-abstraction, raft.go:791-792 only
\* clause stale-term/silence: impl-abstraction — raft_paper_test.go:75-77 says the paper rejects but "Our implementation ignores the request instead"; raft.go:852 "ignore other cases"
\* clause learner-silence: requirement — comment raft.go:126, test raft_test.go:381 TestLearnerCannotVote asserts no message; raft.go:887 TODO says learners may need to vote later
\* clause term reset on a higher-term MsgVote: requirement — Raft-paper §5.1 (a server adopts a larger term it sees); PreVote exception: comment raft.go:803
\* clause grant (single vote, up-to-date): requirement — tests TestFollowerVote, TestVoter, TestRecvMsgVote; comment log.go:273-278
\* clause PreVote grant for a future term despite an existing vote: impl-abstraction — only the narrating comment raft.go:896-897
\* clause response term: requirement for granted responses — comment raft.go:902-910; impl-abstraction for rejections (local term), raft.go:919-920 only
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   narrowed intent to the rule-backed clauses (stale-term handling, PreVote future-term grant and rejection term are impl-abstraction clauses), retyped raft.go:892 comment to impl as narration, added clause lines and "->" suffixes.
VoteDecisionEligibility == \A o\in quality.votes:VoteContract(o)
\* REQ-EVIDENCE CampaignDecisionEligibility
\* intent:   an observed Hup or tick never starts a (pre-)campaign at a leader, a non-voter, or a node with a committed but unapplied configuration change; an eligible timed-out node does start one, sending one vote request to every other voter for term+1 with its last index and term, and a pre-campaign leaves its own term unchanged.
\* status:   mixed
\* evidence: history 9392e5d3b:node.go:141 "it MUST apply all pending configuration changes if there is any." -> no campaign while a committed configuration change is unapplied
\* evidence: history cd227fb83 (raft: hide Campaign rules on applying all entries) "hide Campaign rules on applying all entries" -> the same rule moved from the caller into raft
\* evidence: test source/raft_paper_test.go:141 testNonleaderStartElection "if a follower receives no communication" -> a timed-out non-leader campaigns, one MsgVote per other voter for term+1
\* evidence: comment source/raft.go:126 "It does not vote or promote itself." -> a non-voter (learner) never campaigns
\* evidence: test source/raft_test.go:3880 TestLearnerCampaign "a learner won't campaign even if it receives" -> a non-voter (learner) never campaigns
\* evidence: doc source/doc.go:261 "When Config.PreVote is true, a pre-election is carried out first" -> a pre-campaign leaves its own term unchanged
\* evidence: impl source/raft.go:683 "In particular it does not increase"
\* evidence: impl source/raft.go:751 "this is a single-node cluster). Advance to the next state."
\* evidence: impl source/raft.go:870 "if n := numOfPendingConf(ents); n != 0 && r.raftLog.committed > r.raftLog.applied {"
\* watch:    raft.go:Step (MsgHup); raft.go:campaign; raft.go:tickElection; raft.go:promotable; raft.go:numOfPendingConf; raft.go:becomePreCandidate; raft.go:becomeCandidate
\* verified: V00
\* note:     the pending-configuration rule was a caller MUST in node.go (Advance doc) until cd227fb83 moved it into raft.go:866-873; the code keeps only a log message. raft.go:683 and raft.go:751 are retyped to impl: they narrate becomePreCandidate and the single-node branch. Mixed origins, not splittable (one LET); per-clause status below.
\* clause due/trigger arithmetic and leader tick keeps term: impl-abstraction — only raft.go:619-627 tickElection, raft.go:881-883
\* clause non-voter ignore: requirement — comment raft.go:126; test TestLearnerCampaign
\* clause pending-conf block: requirement — history 9392e5d3b:node.go:141 (rule removed from docs by cd227fb83 and enforced in code)
\* clause compacted-slice fatal: model-internal — models the Panicf at raft.go:866-869
\* clause vote requests (recipients, term+1, last index/term): requirement — test raft_paper_test.go:141-146 (recipients, term); Raft-paper §5.4.1 (RequestVote carries the last log index and term)
\* clause pre-vote keeps term: requirement — doc.go:260-263 (raft.go:682-684 only narrates)
\* clause singleton wins at once: requirement — doc.go:255-256 "If it's more than majority (quorum), it becomes leader" (raft.go:749-751 only narrates)
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, model-internal, requirement); handle clause by clause
\* review:   narrowed intent to exclude the impl-only tick arithmetic, retyped the narrating comments raft.go:683 and raft.go:751 to impl, re-sourced the pre-vote and singleton clauses, added "->" suffixes.
CampaignDecisionEligibility == \A o\in quality.campaigns:CampaignContract(o)
\* REQ-EVIDENCE TransferDecisionEligibility
\* intent:   every observed MsgTransferLeader at a leader ignores unknown and already-pending targets, cancels the transfer on self, otherwise records the target with a reset election timer, and sends MsgTimeoutNow exactly when the target is caught up.
\* status:   mixed
\* evidence: comment source/raft.go:277 "Follow the procedure defined in raft thesis 3.10." -> MsgTimeoutNow is sent once the target is caught up
\* evidence: comment source/raft.go:1173 "Transfer leadership should be finished in one electionTimeout, so reset r.electionElapsed." -> election timer reset when a transfer is recorded
\* evidence: test source/raft_test.go:3317 TestLeaderTransferToUpToDateNode "verifies transferring should succeed" -> a caught-up target receives MsgTimeoutNow and the transfer completes
\* evidence: test source/raft_test.go:3605 TestLeaderTransferSecondTransferToSameNode "should not extend the timeout while the first one is pending." -> an already-pending target is ignored
\* evidence: test source/raft_test.go:3458 TestLeaderTransferToSelf "Transfer leadership to self, there will be noop." -> self target leaves no pending transfer
\* evidence: test source/raft_test.go:3468 TestLeaderTransferToNonExistingNode "Transfer leadership to non-existing node, there will be noop." -> an unknown target is ignored
\* evidence: impl source/raft.go:1176 "if pr.Match == r.raftLog.lastIndex() {"
\* evidence: impl source/raft.go:1152 "if pr.IsLearner {"
\* watch:    raft.go:stepLeader (MsgTransferLeader); raft.go:sendTimeoutNow; raft.go:abortLeaderTransfer; raft.go:tickHeartbeat
\* verified: V00
\* note:     a lagging eligible target is admitted (MsgAppend instead of MsgTimeoutNow). Searched history for the learner guard: log -S'Ignored transferring leadership' gives 26506fa2f (raft: support learner) and a1bcec0c7, no stated rationale. Mixed origins, not splittable (one LET); per-clause status below.
\* clause learner-target ignore: impl-abstraction — impl raft.go:1152-1155 only; introduced by 26506fa2f without rationale
\* clause unknown/same-target ignore and self abort: requirement — tests TestLeaderTransferToNonExistingNode, TestLeaderTransferSecondTransferToSameNode, TestLeaderTransferToSelf
\* clause timer reset on accept: requirement — comment raft.go:1173
\* clause MsgTimeoutNow iff caught up: requirement — comment raft.go:277 (thesis 3.10); test TestLeaderTransferToUpToDateNode
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   narrowed intent to drop the learner-target exclusion, which its own clause line classes impl-abstraction; added "->" suffixes.
TransferDecisionEligibility == \A o\in quality.transfers:TransferContract(o)
\* REQ-EVIDENCE RequestCorrelatedConfigurationEffects
\* intent:   applying a committed configuration entry changes the voter/learner sets as its kind says (no change when cancelled via NodeID zero), and every applied non-bootstrap change comes from a handed-off request with the same kind and target, bootstrap entries being AddVoter entries of the boot peers.
\* status:   mixed
\* evidence: doc source/README.md:120 "may be cancelled at this point by setting the NodeID field to zero" -> a cancelled change leaves the configuration unchanged
\* evidence: doc source/README.md:178 "After config change is committed, some committed entry with type raftpb.EntryConfChange will be returned." -> applied changes are committed entries that come from proposed ConfChanges
\* evidence: comment source/node.go:199 "It appends a ConfChangeAddNode entry for each given peer to the initial log." -> bootstrap entries are AddVoter entries of the boot peers
\* evidence: test source/raft_test.go:3082 TestAddNode "TestAddNode tests that addNode could update nodes correctly." -> AddVoter adds the target to the voters
\* evidence: test source/raft_test.go:3093 TestAddLearner "TestAddLearner tests that addLearner could update nodes correctly." -> AddLearner adds the target to the learners
\* evidence: test source/raft_test.go:3141 TestRemoveNode "TestRemoveNode tests that removeNode could update nodes and" -> Remove removes the target from the voters
\* evidence: impl source/raft.go:1412 "Can only change Learner to Voter."
\* evidence: impl source/raft.go:1403 "func (r *raft) applyConfChange(cc pb.ConfChange) pb.ConfState {"
\* watch:    raft.go:applyConfChange; node.go:run (confc); rawnode.go:ApplyConfChange; node.go:StartNode; rawnode.go:NewRawNode
\* verified: V00
\* note:     the request/handoff witness is model bookkeeping; the bootstrap shape (id 0, term 1, AddVoter of a boot peer) follows node.go:198-225. raft.go:1412 is retyped to impl: it states the code's limitation and is followed by "TODO(tbg): why?", so it gives no rule; log -S'Can only change Learner to Voter' -- raft.go finds only 518a73189 (raft: move more methods onto the progress tracker), a code move by its subject. Mixed origins, not splittable (one LET); per-clause status below.
\* clause add/remove/cancel effect: requirement — README.md:120,178; tests TestAddNode, TestAddLearner, TestRemoveNode
\* clause AddLearner of an existing voter is a no-op: impl-abstraction — raft.go:1412-1415, whose comment is followed by "TODO(tbg): why?"
\* clause entry is committed in the applier's log: requirement — README.md:178; comment node.go:76-78
\* clause request correlation / bootstrap shape: requirement — README.md:172-178 and node.go:199; the handoff flag itself is model-internal
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   narrowed intent to drop the AddLearner-of-a-voter no-op (impl-abstraction per its clause), retyped raft.go:1412 to impl, added "->" suffixes.
RequestCorrelatedConfigurationEffects == \A o\in quality.effects:EffectContract(o)
\* REQ-EVIDENCE ProposalConfigurationDecisions
\* intent:   an observed proposal is dropped in each documented drop case (removed leader, pending transfer, uncommitted quota exceeded, candidate, forwarding disabled), and when a leader accepts it the proposed entries are appended in order with kind, id and target kept, except that a configuration change becomes a no-op while another change is pending or earlier in the same batch.
\* status:   mixed
\* evidence: comment source/raft.go:279 "Only one conf change may be pending (in the log, but not yet" -> a configuration change becomes a no-op while another is pending or earlier in the batch
\* evidence: doc source/README.md:195 "any proposed membership change is simply disallowed while any uncommitted change appears" -> a configuration change is not admitted while another is pending
\* evidence: comment source/node.go:136 "At most one ConfChange can be in the process of going through consensus." -> at most one configuration change in flight
\* evidence: test source/raft_test.go:3035 TestStepIgnoreConfig "the proposal to noop and keep its original state." -> a second configuration change is appended as a no-op
\* evidence: comment source/raft.go:71 "ErrProposalDropped is returned when the proposal is ignored by some cases," -> drop decisions exist and are reported to the proposer
\* evidence: comment source/raft.go:163 "proposals will begin to return ErrProposalDropped" -> drop when the uncommitted quota is exceeded
\* evidence: comment source/raft.go:199 "DisableProposalForwarding set to true means that followers will drop" -> drop at a follower with forwarding disabled
\* evidence: history db2dbe524 (raft: Ignore proposals if not a current member.) "Ignore proposals if not a current member." -> drop at a leader removed from the configuration
\* evidence: doc source/doc.go:224 "When passed to candidate, 'MsgProp' is dropped." -> drop at a candidate
\* evidence: test source/raft_test.go:3517 TestLeaderTransferIgnoreProposal "should return drop proposal error while transferring" -> drop while a transfer is pending
\* evidence: doc source/README.md:170 "If the proposal is committed, data will appear in committed entries" -> accepted entry content (kind, id, target) is kept
\* evidence: impl source/raft.go:969 "drop any new proposals."
\* evidence: impl source/raft.go:977 "for i := range m.Entries {"
\* watch:    raft.go:stepLeader (MsgProp); raft.go:appendEntry; raft.go:increaseUncommittedSize; raft.go:stepFollower (MsgProp); raft.go:stepCandidate (MsgProp); node.go:run (propc)
\* verified: V00
\* note:     each drop condition is documented, but the exact precedence, the follower-without-leader drop and the obligation to accept otherwise are only code; README.md:170 also says "There is no guarantee that a proposed command will be committed". raft.go:969 is retyped to impl (it narrates "if not a member, drop"); the removed-leader rule is instead backed by history db2dbe524 (found with log -S'drop any new proposals'). Not splittable (one LET); per-clause status below.
\* clause conf rewrite to no-op / one pending change: requirement — README.md:195, raft.go:279-284, node.go:136, test TestStepIgnoreConfig
\* clause individual drop conditions (removed, transfer, quota, candidate, forwarding disabled): requirement — raft.go:71,163,199, history db2dbe524, doc.go:224, test TestLeaderTransferIgnoreProposal
\* clause follower-without-leader drop, decision precedence and mandatory acceptance: impl-abstraction — raft.go:962-994, 1199-1201, 1235-1244 only
\* clause accepted content preserved (kind, id, target): requirement — README.md:170 "data will appear in committed entries"
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   status impl-abstraction -> requirement by narrowing intent to the documented clauses (precedence and mandatory acceptance stay impl-abstraction clauses), retyped raft.go:969 to impl, added history db2dbe524, re-quoted README.md:170 to the sentence that supports the intent.
ProposalConfigurationDecisions == \A o\in quality.proposals:ProposalContract(o)

\* node.go:198-245, rawnode.go:72-116. Constructor bootstrap is atomic.
InitialRaft(n,timeout) ==
    LET joining==n\in Joining
        h==IF joining THEN <<>> ELSE BootLog
        cfg==IF joining THEN EmptyConfig ELSE BootConfig
    IN [id |-> n, alive |-> TRUE, incarnation |-> 0, term |-> 1, vote |-> 0,
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
         Won(rs[j].config.voters,{p \in rs[j].config.voters:
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
    /\ (kind="Read" => \A j\in RequestId:
           requests[j].status#"Unused" /\ requests[j].kind="Read" => requests[j].context#ctx)
    /\ (kind\in {"AddVoter","AddLearner"} =>
           ~\E h\in history.applied:\E k\in DOMAIN h:
               h[k].kind="Remove" /\ h[k].target=target /\ h[k].id\notin CancelChanges /\
               target\in ConfigOf(Prefix(h,k-1)).voters\cup ConfigOf(Prefix(h,k-1)).learners)
    /\ parent=0 \/ (parent\in RequestId /\ requests[parent].status#"Unused")
    /\ requests'=[requests EXCEPT ![id]=[EmptyRequest EXCEPT !.status="Invoked",
        !.node=n, !.kind=kind, !.target=target, !.weight=w, !.encoded=z,
        !.parent=parent, !.context=ctx, !.beforeWrites=history.writes]]
    /\ UNCHANGED <<raft,disk,ready,application,wire,history>>
\* Handoff and core work are one serialized Node select/RawNode call; result is later.
ProtocolPropose(n,id,timeout) ==
    /\ Live(n) /\ requests[id].status="Invoked" /\ requests[id].node=n
    /\ requests[id].kind\in Kinds
    /\ n\in RawNodes \/ raft[n].propcEnabled
    /\ LET q==requests[id]
           m==[Message("MsgProp",n,n,0) EXCEPT !.request=id,
                 !.entries= <<Entry(0,0,q.kind,id,q.target,q.weight,q.encoded)>>]
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
       /\ ContainsUpdates(b)
       /\ ready'=[ready EXCEPT ![n]=b]
       /\ raft'=[raft EXCEPT ![n]=[r EXCEPT !.out=EmptyBag,
            !.quota=Max(0,@-Weight(b.committed)), !.readySeq=b.id,
            !.readStates=IF n\in RawNodes THEN @ ELSE <<>>,
            !.prevHS=IF n\in RawNodes THEN @ ELSE b.hs,
            !.prevSS=IF n\in RawNodes THEN @ ELSE b.ss]]
       /\ application'=[application EXCEPT ![n].reads=@\o b.reads]
       /\ history'=Observe([history EXCEPT !.readyChecks=@\cup
              {[from |-> r.applied, first |-> First(r), cursor |-> b.cursor,
                entries |-> b.committed, snapshot |-> b.snapshot.index,
                commit |-> r.commit]}],raft',disk,"Ready")
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
\* log_unstable.go:77-89,111-114: matching captured endpoint only.
AdvanceCore(r,b,n) ==
    LET a==AppliedTo(r,b.cursor)
        last==IF b.entries= <<>> THEN MissingEntry(0) ELSE b.entries[Len(b.entries)]
        stable==b.entries# <<>> /\ last.index>=r.uoff /\ last.index<=Last(r) /\
                 Term(r,last.index)=last.term
    IN [a EXCEPT
        !.unstable=IF stable THEN Suffix(@,last.index+2-r.uoff) ELSE @,
        !.uoff=IF stable THEN last.index+1 ELSE @,
        !.usnap=IF b.snapshot.index>0 /\ r.usnap.index=b.snapshot.index THEN EmptySnapshot ELSE @,
        !.prevHS=IF n\in RawNodes THEN b.hs ELSE @,
        !.prevSS=IF n\in RawNodes THEN b.ss ELSE @,
        !.readStates=IF n\in RawNodes /\ b.reads# <<>> THEN <<>> ELSE @]
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
              cursor |-> b.cursor, applied |-> a.applied]}],raft',disk,"Advance")
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
           b==WrapperLoop(IF n\notin RawNodes /\ e.target=n /\ e.id\notin CancelChanges /\ n\notin Members(b0)
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
\* newRaft/loadState and rawnode.go:85-114. Raw empty-log inference is preserved.
RestartCore(n,timeout) ==
    LET d==disk[n] h==DiskHist(d)
        app==IF RecoveryMode="AppliedAdapter" THEN d.savedApp ELSE d.snapshot.hist
        cfg==IF RecoveryMode="AppliedAdapter" THEN ConfigOf(app) ELSE d.snapshot.config
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
        fresh==n\in RawNodes /\ Len(h)=0
        e==IF fresh THEN BecomeFollower(c,1,0,timeout) ELSE c
    IN [e EXCEPT !.prevHS=IF n\in RawNodes /\ ~fresh THEN HS(e) ELSE EmptyHS,
                 !.prevSS=SS(e)]
ProtocolRestart(n,timeout) ==
    /\ ~raft[n].alive
    /\ LET a==RestartCore(n,timeout) d==disk[n]
           app==IF RecoveryMode="AppliedAdapter" THEN d.savedApp ELSE d.snapshot.hist
       IN /\ raft'=[raft EXCEPT ![n]=a]
          /\ application'=[application EXCEPT ![n]=[EmptyApp EXCEPT !.hist=app, !.config=ConfigOf(app)]]
          /\ history'=Observe([history EXCEPT !.recovery=@\cup
              {[savedTerm |-> d.hs.term, savedVote |-> d.hs.vote, term |-> a.term, vote |-> a.vote,
                commit |-> a.commit, hist |-> Hist(a), fatal |-> a.fatal,
                diskHist |-> DiskHist(d), app |-> app]}],raft',disk,"Restart")
    /\ UNCHANGED <<disk,ready,requests,wire>>

(***************************************************************************
Independent safety contracts. Ghost observations never guard core actions.
Properties are reusable over all scenarios, including crashes and snapshots.
***************************************************************************)
\* Brief §5; source: raft.go:693-726, quorum/majority.go:170-201.
\* REQ-EVIDENCE ElectionSafety
\* intent:   at most one node ever wins an election in any given term.
\* status:   requirement
\* evidence: protocol Raft-paper §5.2 "at most one leader can be elected in a given term" -> the whole intent
\* evidence: test source/raft_paper_test.go:234 TestFollowerVote "each follower will vote for at most one" -> one vote per voter per term (ingredient)
\* evidence: test source/raft_paper_test.go:186 TestLeaderElectionInOneRoundRPC "tests all cases that may happen in" -> a win needs a majority of votes (ingredient)
\* evidence: impl source/quorum/majority.go:194 "q := len(c)/2 + 1"
\* evidence: impl source/raft.go:893 "canVote := r.Vote == m.From ||"
\* watch:    raft.go:Step (MsgVote); raft.go:becomeLeader; raft.go:poll; tracker/tracker.go:TallyVotes; quorum/majority.go:VoteResult; raft.go:loadState
\* verified: V00
\* note:     checked over the ghost history.wins recorded in BecomeLeader; across restarts it relies on the durable vote (VoteRecovery).
\* review:   ok
ElectionSafety == \A a,b\in history.wins:a.term=b.term => a.node=b.node
\* REQ-EVIDENCE LogMatching
\* intent:   if two nodes' logs hold an entry with the same index and the same nonzero term, the logs are identical up to that index.
\* status:   requirement
\* evidence: protocol Raft-paper §5.3 "the logs are identical in all entries up through the given index" -> the whole intent
\* evidence: test source/raft_paper_test.go:596 TestFollowerCheckMsgApp "if the follower does not find an" -> consistency check that maintains matching prefixes
\* evidence: test source/raft_paper_test.go:694 TestLeaderSyncFollowerLog "the leader could bring a follower's log" -> follower logs converge to the leader's prefix
\* evidence: impl source/log.go:89 "if l.matchTerm(index, logTerm) {"
\* watch:    log.go:maybeAppend; log.go:findConflict; log.go:matchTerm; log_unstable.go:truncateAndAppend; raft.go:handleAppendEntries; raft.go:maybeSendAppend
\* verified: V00
\* note:     compares Hist including ghost prefixes below compaction; the term>0 guard skips compaction placeholders.
\* review:   ok
LogMatching == \A n,p\in Server:
    \A k\in 1..Min(Last(raft[n]),Last(raft[p])):
       (Hist(raft[n])[k].term=Hist(raft[p])[k].term /\ Hist(raft[n])[k].term>0)
          => Prefix(Hist(raft[n]),k)=Prefix(Hist(raft[p]),k)
\* REQ-EVIDENCE LeaderCompleteness
\* intent:   every leader elected in a term later than a commitment's term holds that committed prefix in its log when elected.
\* status:   requirement
\* evidence: protocol Raft-paper §5.4 "that entry will be present in the logs of the leaders" -> the whole intent
\* evidence: test source/raft_paper_test.go:820 TestVoter "the voter denies its vote if its own log is more up-to-date" -> voters only elect up-to-date candidates (ingredient)
\* evidence: test source/raft_paper_test.go:865 TestLeaderOnlyCommitsLogFromCurrentTerm "only log entries from the leader" -> commitment rule the argument relies on (ingredient)
\* evidence: comment source/log.go:275 "If the logs have last entries with different terms, then the log with the" -> definition of up-to-date used by elections (ingredient)
\* evidence: impl source/log.go:292 "if maxIndex > l.committed && l.zeroTermOnErrCompacted(l.term(maxIndex)) == term {"
\* watch:    log.go:isUpToDate; log.go:maybeCommit; raft.go:maybeCommit; raft.go:Step (MsgVote); raft.go:becomeLeader
\* verified: V00
\* note:     obligations include durable-quorum commitments, commit indexes announced in published messages and completed client writes (base.tla DurableObligations, ProtocolPublish, ProtocolCompleteWrite).
\* review:   ok
LeaderCompleteness == \A w\in history.wins:\A c\in history.obligations:
                         w.term>c.term => Covers(w.hist,c.hist)
\* REQ-EVIDENCE CommittedHistory
\* intent:   a live node never loses entries it has committed, and all observed commitments and every live node's committed prefix lie on one common history.
\* status:   requirement
\* evidence: protocol Raft-paper §5.4.3 "no other server will ever apply a different log entry for the same index" -> all commitments lie on one history
\* evidence: comment source/log.go:32 "committed is the highest log position that is known to be in" -> committed means durably replicated on a quorum
\* evidence: comment source/log.go:200 "never decrease commit" -> a node's commit index never moves back
\* evidence: test source/log_test.go:230 TestLogMaybeAppend "conflict with existing committed entry" -> a committed entry is never overwritten (asserted panic)
\* evidence: test source/log_test.go:450 TestCommitTo "never decrease" -> a node's commit index never moves back
\* evidence: impl source/log.go:95 "conflict with committed entry"
\* evidence: impl source/log.go:111 "after(%d) is out of range [committed(%d)]"
\* watch:    log.go:maybeAppend; log.go:append; log.go:commitTo; log_unstable.go:truncateAndAppend; raft.go:restore; log.go:restore
\* verified: V00
\* note:     the three conjuncts share one origin (State Machine Safety); liveOK is tracked per live incarnation in SetCore.
\* review:   ok
CommittedHistory == /\ history.liveOK
    /\ \A a,b\in history.obligations:Compatible(a.hist,b.hist)
    /\ \A n\in Server:\A c\in history.obligations:
         raft[n].alive => Compatible(Prefix(Hist(raft[n]),raft[n].commit),c.hist)
\* REQ-EVIDENCE AppliedAgreement
\* intent:   any two state-machine histories ever applied, at any nodes, are prefix-compatible.
\* status:   requirement
\* evidence: protocol Raft-paper §5.4.3 "no other server will ever apply a different log entry for the same index" -> the whole intent
\* evidence: doc source/README.md:4 "The state machine is kept in sync through the use of a replicated log." -> applied state machines agree
\* evidence: test source/raft_paper_test.go:545 TestFollowerCommitEntry "it applies the entry to its local state machine (in log order)." -> entries are applied in log order
\* evidence: impl source/log.go:151 "func (l *raftLog) nextEnts() (ents []pb.Entry) {"
\* watch:    log.go:nextEnts; node.go:newReady; raft.go:restore; log.go:restore; node.go:run (advancec)
\* verified: V00
\* review:   ok
AppliedAgreement == \A a,b\in history.applied:Compatible(a,b)
\* Durable term/vote promises survive constructor; no equality to volatile votes.
\* REQ-EVIDENCE VoteRecovery
\* intent:   after a restart a node's term is never below its persisted term, and in the persisted term it keeps its persisted vote.
\* status:   requirement
\* evidence: comment source/node.go:599 "(Updated on stable storage before responding to RPCs)" -> term and vote are persistent state that must survive restarts
\* evidence: comment source/raft.go:143 "raft reads out the previous state and configuration" -> a restarted node recovers its persisted state
\* evidence: doc source/README.md:116 "Write Entries, HardState and Snapshot to persistent storage in order" -> HardState (term, vote) is persisted by the caller
\* evidence: test source/node_test.go:656 TestNodeRestart "storage.SetHardState(st)" -> a restarted node reports the persisted HardState (term; vote is zero in the test)
\* evidence: impl source/raft.go:1502 "r.Term = state.Term"
\* watch:    raft.go:newRaft; raft.go:loadState; raft.go:becomeFollower; rawnode.go:NewRawNode; node.go:RestartNode
\* verified: V00
\* note:     RawNode with an empty Storage log re-bootstraps via becomeFollower(1, None) (rawnode.go:89-90) even if a HardState exists; see out/concerns.md.
\* review:   ok
VoteRecovery == \A x\in history.recovery:
    x.term>=x.savedTerm /\ (x.term=x.savedTerm /\ x.savedVote#0 => x.vote=x.savedVote)
\* REQ-EVIDENCE RecoveryBacking
\* intent:   on restart the recovered commit index is backed by durable log entries without gaps, and the recovered application state is a prefix of the durable log.
\* status:   requirement
\* evidence: doc source/README.md:116 "Entries first, then HardState and Snapshot if they are not empty" -> the persisted commit index is backed by entries written before it
\* evidence: doc source/README.md:124 "all persisted log entries must be made available via an implementation of the Storage interface" -> the durable log is what recovery reads
\* evidence: comment source/node.go:77 "These have previously been committed to stable" -> entries handed to the application are durable, so applied state is a durable prefix
\* evidence: impl source/raft.go:1499 "state.commit %d is out of range"
\* evidence: impl source/log.go:203 "Was the raft log corrupted, truncated, or lost?"
\* watch:    raft.go:loadState; raft.go:newRaft; log.go:newLogWithSize; storage.go:Append; storage.go:ApplySnapshot; storage.go:InitialState
\* verified: V00
\* note:     the application-prefix conjunct matters for RecoveryMode="AppliedAdapter" (Config.Applied, raft.go:146-150); in Replay mode it holds by construction.
\* review:   ok
RecoveryBacking == \A x\in history.recovery:
    /\ x.commit<=Len(x.diskHist)
    /\ \A k\in 1..x.commit:x.diskHist[k].kind#"Missing"
    /\ Covers(x.diskHist,x.app)
\* REQ-EVIDENCE PromiseBacking
\* intent:   every message or write acknowledgement released to the outside is backed by durable state (term, granted vote, acknowledged log prefix, announced commit prefix).
\* status:   requirement
\* evidence: doc source/README.md:118 "no messages be sent until the latest HardState has been persisted to disk" -> messages backed by durable term, vote and earlier entries
\* evidence: comment source/node.go:58 "The current state of a Node to be saved to stable storage BEFORE" -> messages backed by durable HardState
\* evidence: comment source/node.go:69 "Entries specifies entries to be saved to stable storage BEFORE" -> messages backed by the durable log prefix they acknowledge or announce
\* evidence: comment source/node.go:599 "(Updated on stable storage before responding to RPCs)" -> responses backed by durable term, vote and log
\* evidence: comment source/node.go:77 "These have previously been committed to stable" -> a write acknowledged after application is backed by the durable log
\* evidence: impl source/node.go:603 "return entsnum != 0 || st.Vote != prevst.Vote || st.Term != prevst.Term"
\* watch:    node.go:Ready (field contracts); node.go:newReady; node.go:MustSync; rawnode.go:Ready; raft.go:send; raft.go:sendHeartbeat; raft.go:handleAppendEntries
\* verified: V00
\* note:     backing is defined in PromiseOK. README.md:118 also allows "Messages may be sent while entries from the same batch are being persisted" (SendPolicy="SameBatch"); see out/concerns.md. The write-result promise (ProtocolCompleteWrite) is an application-level promise checked the same way.
\* review:   added node.go:77 as evidence because no cited non-impl line covered the write-acknowledgement part of the intent; added "->" suffixes.
PromiseBacking == \A p\in history.promises:p.backed
\* README.md:120,193. Configuration has a committed/constructor/snapshot origin.
\* REQ-EVIDENCE ConfigurationOrigin
\* intent:   every live node's configuration is exactly the result of the configuration entries in a committed prefix of its own log (bootstrap, applied entries or restored snapshot).
\* status:   requirement
\* evidence: doc source/README.md:193 "the membership change takes effect when its entry is applied" -> configuration is the result of applied configuration entries
\* evidence: doc source/README.md:178 "After config change is committed, some committed entry with type raftpb.EntryConfChange will be returned." -> only committed entries are applied
\* evidence: comment source/node.go:160 "Returns an opaque ConfState protobuf which must be recorded" -> a restored snapshot carries the configuration of its prefix
\* evidence: impl source/raft.go:1403 "func (r *raft) applyConfChange(cc pb.ConfChange) pb.ConfState {"
\* watch:    raft.go:applyConfChange; raft.go:restore; raft.go:newRaft; node.go:StartNode; rawnode.go:NewRawNode; node.go:run (confc)
\* verified: V00
\* review:   ok
ConfigurationOrigin == \A n\in Server:
    raft[n].alive =>
       /\ raft[n].config=ConfigOf(raft[n].cfgHist)
       /\ Covers(Hist(raft[n]),raft[n].cfgHist)
       /\ Len(raft[n].cfgHist)<=raft[n].commit
\* Each configuration entry must commit using its predecessor voter configuration.
\* Bootstrap entries (id=0) are explicit constructor axioms, not quorum decisions.
\* REQ-EVIDENCE ConfigurationTransitionSafety
\* intent:   every non-bootstrap configuration entry is committed under exactly the voter set produced by all entries before it (one change at a time, committed under the old membership).
\* status:   requirement
\* evidence: doc source/README.md:193 "so the entry is committed under the old membership instead of the new" -> committed under the voter set before it
\* evidence: doc source/README.md:195 "any proposed membership change is simply disallowed while any uncommitted change appears" -> one change at a time
\* evidence: comment source/raft.go:279 "Only one conf change may be pending (in the log, but not yet" -> one change at a time
\* evidence: test source/raft_test.go:3035 TestStepIgnoreConfig "the proposal to noop and keep its original state." -> a second pending change is not admitted
\* evidence: test source/raft_test.go:3058 TestNewLeaderPendingConfig "new leader sets its pendingConfigIndex" -> a new leader keeps the one-at-a-time gate
\* evidence: impl source/raft.go:980 "if r.pendingConfIndex > r.raftLog.applied {"
\* watch:    raft.go:stepLeader (MsgProp); raft.go:becomeLeader (pendingConfIndex); raft.go:applyConfChange; raft.go:maybeCommit; raft.go:Step (MsgHup pending-conf check)
\* verified: V00
\* note:     gating uses the applied index, so safety also depends on the campaign rule in CampaignDecisionEligibility.
\* review:   ok
ConfigurationTransitionSafety == \A c\in history.commitUses:
    \A k\in (c.oldCommit+1)..Len(c.hist):
       (c.hist[k].kind\in ConfKinds /\ c.hist[k].id#0) =>
             c.voters=ConfigOf(Prefix(c.hist,k-1)).voters
\* REQ-EVIDENCE LearnerEligibility
\* intent:   a node never grants a (pre-)vote and never starts a campaign while it is a learner.
\* status:   requirement
\* evidence: comment source/raft.go:126 "It does not vote or promote itself." -> the whole intent
\* evidence: test source/raft_test.go:381 TestLearnerCannotVote "a learner can't vote even it receives a valid Vote request." -> no vote granted by a learner
\* evidence: test source/raft_test.go:309 TestLearnerElectionTimeout "should not start election even" -> no campaign by a learner on timeout
\* evidence: test source/raft_test.go:3880 TestLearnerCampaign "a learner won't campaign even if it receives" -> no campaign by a learner on Hup or MsgTimeoutNow
\* evidence: impl source/raft.go:886 "if r.isLearner {"
\* evidence: impl source/raft.go:1400 "return pr != nil && !pr.IsLearner"
\* watch:    raft.go:Step (MsgVote, MsgHup); raft.go:promotable; raft.go:stepFollower (MsgTimeoutNow); raft.go:campaign; raft.go:applyConfChange (isLearner)
\* verified: V00
\* note:     raft.go:887 TODO "learner may need to vote" signals the rule may be revisited.
\* review:   ok
LearnerEligibility == /\ \A x\in history.grants:~x.learner
                      /\ \A x\in history.campaigns:~x.learner
\* REQ-EVIDENCE QuorumAccounting
\* intent:   every election win and every commit decision is backed by a majority of the voter set it was decided in.
\* status:   mixed
\* evidence: protocol Raft-paper §5.2 "receives votes from a majority of the servers" -> election wins need a majority
\* evidence: test source/raft_paper_test.go:472 TestLeaderAcknowledgeCommit "replicated it on a majority of the servers" -> commit decisions need a majority
\* evidence: test source/raft_paper_test.go:186 TestLeaderElectionInOneRoundRPC "tests all cases that may happen in" -> election wins need a majority
\* evidence: impl source/quorum/majority.go:162 "pos := n - (n/2 + 1)"
\* evidence: impl source/quorum/majority.go:194 "q := len(c)/2 + 1"
\* watch:    quorum/majority.go:VoteResult; quorum/majority.go:CommittedIndex; tracker/tracker.go:Committed; tracker/tracker.go:TallyVotes; raft.go:maybeCommit; raft.go:applyConfChange
\* verified: V00
\* note:     the nonempty-voters conjunct is stricter than the code convention at quorum/majority.go:172 ("By convention, the elections on an empty config win"); see out/concerns.md. matches\subseteq voters holds by construction of the commitUses ghost.
\* clause majority of wins and commits: requirement — Raft-paper §5.2, tests TestLeaderAcknowledgeCommit, TestLeaderElectionInOneRoundRPC
\* clause voters#{} for wins and commits: unknown — no non-impl evidence; quorum/majority.go:172-174 states the opposite convention for elections
\* clause c.matches\subseteq c.voters: model-internal — true by construction of the commitUses ghost
\* relabel:  requirement -> mixed (clause statuses: model-internal, requirement, unknown); handle clause by clause
\* review:   narrowed intent to drop the nonempty-voter-set claim, which no evidence supports and a code comment contradicts; recorded it and the subset check as clause lines; added "->" suffixes.
QuorumAccounting ==
    /\ \A w\in history.wins:w.voters#{} /\ Won(w.voters,w.yes)
    /\ \A c\in history.commitUses:c.voters#{} /\ c.matches\subseteq c.voters /\ Won(c.voters,c.matches)
\* raft.go:613 versus 1039-1091: distinguish self's volatile evidence.
\* REQ-EVIDENCE ReplicationEvidence
\* intent:   whenever a leader records Match m>0 for a peer, that peer actually acknowledged a log whose first m entries are still a prefix of the leader's log.
\* status:   requirement
\* evidence: doc source/design.md:7 "`match` is the index of the highest known matched entry." -> Match reflects an acknowledged matching prefix
\* evidence: doc source/design.md:48 "which implies that it has matched the index sent." -> Match is set from a follower's acknowledgement
\* evidence: comment source/tracker/progress.go:138 "MaybeUpdate is called when an MsgAppResp arrives from the follower, with the" -> Match is raised only by a follower's acknowledgement
\* evidence: protocol Raft-paper §5.3 "a leader never overwrites or deletes entries in its log" -> the acknowledged prefix stays a prefix of the leader's log
\* evidence: impl source/raft.go:1054 "if pr.MaybeUpdate(m.Index) {"
\* watch:    tracker/progress.go:MaybeUpdate; raft.go:stepLeader (MsgAppResp); raft.go:handleAppendEntries; raft.go:handleSnapshot; raft.go:reset; tracker/tracker.go:InitProgress
\* verified: V00
\* note:     the leader itself is excluded: its own Match is volatile (raft.go:613).
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
\* intent:   every snapshot created by the caller, held as unstable snapshot, or persisted carries index, term and ConfState consistent with the log prefix it captures.
\* status:   requirement
\* evidence: comment source/storage.go:189 "can be used to reconstruct the state at that point." -> index and term match the captured prefix
\* evidence: comment source/storage.go:191 "the result of the last ApplyConfChange must be passed in." -> ConfState matches the captured prefix
\* evidence: comment source/node.go:160 "Returns an opaque ConfState protobuf which must be recorded" -> ConfState matches the captured prefix
\* evidence: test source/storage_test.go:190 TestStorageCreateSnapshot "pb.SnapshotMetadata{Index: 4, Term: 4, ConfState: *cs}" -> created snapshot carries the entry's index, term and given ConfState
\* evidence: impl source/storage.go:205 "ms.snapshot.Metadata.Term = ms.ents[i-offset].Term"
\* watch:    storage.go:CreateSnapshot; storage.go:ApplySnapshot; raft.go:restore; log_unstable.go:restore; node.go:ApplyConfChange
\* verified: V00
\* note:     ConfState correctness depends on the caller passing the latest ApplyConfChange result (storage.go:190-191); the model derives it from applied history.
\* review:   ok
SnapshotBacking ==
    /\ \A s\in history.snapshots:SnapshotValid(s)
    /\ \A n\in Server:SnapshotValid(raft[n].usnap) /\ SnapshotValid(disk[n].snapshot)
\* REQ-EVIDENCE AckPreservation_LogUnchanged
\* intent:   acknowledging a Ready with Advance never makes the node lose or revert log entries written after that Ready (entries are marked stable only if their index and term still match).
\* status:   mixed
\* evidence: history ee0757a9b (raft: stableTo checks term matching) "raft must verify the (index,term) of stableTo, before marking the entries as stable." -> Advance must not mark entries stable after they were truncated and replaced
\* evidence: test source/log_test.go:481 TestStableTo "// bad term" -> a term mismatch leaves the unstable entries in place
\* evidence: impl source/log_unstable.go:83 "only update the unstable entries if term is matched with"
\* evidence: impl source/log_unstable.go:85 "if gt == t && i >= u.offset {"
\* watch:    log_unstable.go:stableTo; log.go:stableTo; node.go:run (advancec); rawnode.go:commitReady
\* verified: V00
\* note:     split from AckPreservation (clause 1). The formula checks full equality of the logical log before and after Advance; the evidence only says Advance must not wrongly stabilise truncated entries. log_unstable.go:83 is retyped to impl (it narrates the next line); README.md:124 was removed because it says nothing about Advance.
\* clause log equality beyond the stableTo term check (Advance changes nothing else in the log): impl-abstraction — log_unstable.go:77-89, node.go:run and rawnode.go:commitReady only
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction); handle clause by clause
\* review:   narrowed intent from "never changes the log" to the stableTo term-match rule the history supports, recorded full equality as an impl-abstraction clause, retyped log_unstable.go:83 to impl, removed README.md:124.
AckPreservation_LogUnchanged == \A a\in history.acks:
    /\ a.before=a.after
\* REQ-EVIDENCE AckPreservation_SnapshotRetained
\* intent:   Advance never discards an unstable snapshot other than the one carried by the acknowledged Ready.
\* status:   unknown
\* evidence: impl source/log_unstable.go:112 "if u.snapshot != nil && u.snapshot.Metadata.Index == i {"
\* watch:    log_unstable.go:stableSnapTo; log.go:stableSnapTo; node.go:run (prevSnapi); rawnode.go:commitReady
\* verified: V00
\* note:     split from AckPreservation (clause 2). Searched log -S'stableSnapTo' (83245f7fe, 4b3a7ff35, 09d237400) and log -S'Metadata.Index == prevSnapi' (516891c49): code moves only, no comment or commit message explains the index-equality guard; no *_test.go calls stableSnapTo. Looks like a durability requirement but only impl evidence found. The commit 516891c49 ("raft: set snapshot to nil when it is saved") only narrates the change and was removed as evidence; Review re-ran log -S'stableSnapTo' -- log_unstable.go log.go node.go rawnode.go raft.go (4b3a7ff35, 83245f7fe) and log -S'Metadata.Index == i' -- log_unstable.go (83245f7fe): no rationale found.
\* review:   removed the history line 516891c49, whose message only narrates the code change; status unknown kept.
AckPreservation_SnapshotRetained == \A a\in history.acks:
    /\ (a.oldSnap#0 /\ a.oldSnap#a.batchSnap => a.afterSnap=a.oldSnap)
\* REQ-EVIDENCE AckPreservation_AppliedCursor
\* intent:   after Advance a node's applied index equals the applied cursor of the acknowledged Ready (last committed entry, else snapshot index).
\* status:   requirement
\* evidence: comment source/node.go:112 "appliedCursor extracts from the Ready the highest index the client has" -> the cursor is what the client has applied once Advance confirms it
\* evidence: comment source/node.go:149 "Advance notifies the Node that the application has saved progress up to the last Ready." -> applied index is set to the progress of the acknowledged Ready
\* evidence: test source/rawnode_test.go:465 TestRawNodeCommitPaginationAfterRestart "its internal applied index cursor to 10 (when it should be 9)" -> applied index must equal the last delivered entry (the test asserts no gap)
\* evidence: impl source/rawnode.go:52 "If entries were applied (or a snapshot), update our cursor for"
\* evidence: impl source/node.go:411 "r.raftLog.appliedTo(applyingToI)"
\* watch:    node.go:appliedCursor; node.go:run (advancec); rawnode.go:commitReady; log.go:appliedTo
\* verified: V00
\* note:     split from AckPreservation (clause 3). rawnode.go:52 is retyped to impl: it narrates the following lines.
\* review:   retyped the narrating comment rawnode.go:52 to impl; intent and status unchanged; added "->" suffixes.
AckPreservation_AppliedCursor == \A a\in history.acks:
    /\ (a.cursor#0 => a.applied=a.cursor)

\* REQ-EVIDENCE AckPreservation
\* intent:   conjunction of the parts below; kept so existing configs and references still work
\* status:   model-internal
\* verified: V00
\* note:     split by origin into AckPreservation_LogUnchanged (requirement), AckPreservation_SnapshotRetained (unknown), AckPreservation_AppliedCursor (requirement)
\* review:   ok
AckPreservation == AckPreservation_LogUnchanged /\ AckPreservation_SnapshotRetained /\ AckPreservation_AppliedCursor
\* REQ-EVIDENCE ReadyAccounting
\* intent:   no ReadState produced for the application is dropped before delivery, and every Ready's committed-entry page starts right after max(applied, snapshot), is contiguous, ends at the cursor and never passes the commit index.
\* status:   requirement
\* evidence: comment source/node.go:168 "ReadIndex request a read state. The read state will be set in the ready." -> no ReadState is dropped before delivery
\* evidence: comment source/log.go:149 "If applied is smaller than the index of snapshot, it returns all committed" -> page starts right after max(applied, snapshot)
\* evidence: comment source/node.go:77 "These have previously been committed to stable" -> page never passes the commit index
\* evidence: test source/rawnode_test.go:466 TestRawNodeCommitPaginationAfterRestart "the next Ready asks the app to apply index 11 (omitting index 10), losing a" -> pages are contiguous across Readies (asserts no gap)
\* evidence: test source/rawnode_test.go:240 TestRawNodeReadIndex "It also ensures that ReadState can be read out." -> ReadStates are delivered in the Ready
\* evidence: impl source/log.go:152 "off := max(l.applied+1, l.firstIndex())"
\* evidence: impl source/rawnode.go:68 "rn.raft.readStates = nil"
\* watch:    node.go:newReady; log.go:nextEnts; log.go:slice; util.go:limitSize; rawnode.go:commitReady (readStates reset); node.go:run (readyc, r.readStates = nil)
\* verified: V00
\* note:     both conjuncts are requirement-backed, so no split; the no-lost-reads evidence is only the API promise at node.go:168 / rawnode.go:276, and the RawNode reset was added by b1eed3342 (raft: add read index for RawNode) without rationale. The quote for rawnode_test.go:240 is at line 238 (the test's doc comment).
\* review:   ok
ReadyAccounting ==
    /\ history.lostReads={}
    /\ \A b\in history.readyChecks:
        /\ b.cursor<=b.commit
        /\ IF b.entries= <<>> THEN b.cursor=b.snapshot ELSE
             /\ Head(b.entries).index=Max(b.from+1,b.first)
             /\ b.cursor=b.entries[Len(b.entries)].index
             /\ \A k\in DOMAIN b.entries:b.entries[k].index=Head(b.entries).index+k-1
\* tracker/inflights.go:43-124: endpoints ordered, quota is not wire cardinality.
\* REQ-EVIDENCE QuotaIntegrity
\* intent:   the uncommitted-size quota is nonnegative and, at a leader, never exceeds the payload of its unapplied log tail, and every progress holds at most MaxInflight in-flight append indexes in increasing order.
\* status:   mixed
\* evidence: comment source/raft.go:1560 "log tail but will never overestimate it. Saturate at 0 instead of" -> quota nonnegative and never above the (uncommitted, hence unapplied) tail
\* evidence: comment source/tracker/inflights.go:44 "Full() must be called prior to Add() to verify that there is room" -> at most MaxInflight in-flight indexes
\* evidence: comment source/tracker/inflights.go:46 "monotonic sequence of indexes." -> in-flight indexes in increasing order
\* evidence: comment source/tracker/progress.go:68 "The index MUST be added" -> in-flight indexes in increasing order
\* evidence: comment source/raft.go:166 "MaxInflightMsgs limits the max number of in-flight append messages during" -> at most MaxInflight in-flight indexes
\* evidence: doc source/design.md:57 "limit the # of in flight messages < N when in `replicate` state." -> bounded number of in-flight indexes
\* evidence: test source/raft_test.go:183 TestUncommittedEntryLimit "expect them, or because the final tally ends up nonzero." -> quota returns to zero once entries commit (no overestimate)
\* evidence: impl source/raft.go:1536 "if r.uncommittedSize > 0 && r.uncommittedSize+s > r.maxUncommittedSize {"
\* watch:    raft.go:increaseUncommittedSize; raft.go:reduceUncommittedSize; raft.go:becomeLeader; node.go:run (readyc); rawnode.go:Ready; tracker/inflights.go:Add; tracker/inflights.go:FreeLE; raft.go:maybeSendAppend
\* verified: V00
\* note:     the comment bounds the uncommitted tail; the model checks the weaker unapplied-tail bound because the code only reduces the quota when entries leave in Ready.CommittedEntries (node.go:407, rawnode.go:189). The formula checks strictly increasing indexes; "monotonic" and "in order" do not exclude repeats, and log -S'monotonic sequence' only finds 1dc601a9b (package extraction). Not splittable at the shape allowed (the order check is nested under \A p).
\* clause quota bounds and inflight count: requirement — raft.go:1559-1561, inflights.go:44, raft.go:166
\* clause inflight order (non-decreasing): requirement — inflights.go:45-46, progress.go:67-69
\* clause strictness of the order (no repeated index): impl-abstraction — no non-impl evidence; follows from maybeSendAppend only
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   narrowed "strictly increasing" to "increasing" because the comments say only "monotonic"/"in order"; strictness recorded as an impl-abstraction clause; added "->" suffixes.
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
\* intent:   every proposal handed to raft is dropped in each documented drop case (removed leader, pending transfer, uncommitted quota exceeded, candidate, forwarding disabled at a follower), and a follower with a known leader and forwarding enabled forwards it.
\* status:   mixed
\* evidence: comment source/raft.go:71 "ErrProposalDropped is returned when the proposal is ignored by some cases," -> drop decisions exist and are reported to the proposer
\* evidence: comment source/raft.go:163 "proposals will begin to return ErrProposalDropped" -> drop when the uncommitted quota is exceeded
\* evidence: comment source/raft.go:199 "DisableProposalForwarding set to true means that followers will drop" -> drop at a follower with forwarding disabled
\* evidence: history db2dbe524 (raft: Ignore proposals if not a current member.) "Ignore proposals if not a current member." -> drop at a leader removed from the configuration
\* evidence: doc source/doc.go:224 "When passed to candidate, 'MsgProp' is dropped." -> drop at a candidate
\* evidence: test source/node_test.go:211 TestDisableProposalForwarding "proposals are not forwarded to" -> forwarding disabled drops; forwarding enabled forwards (both asserted)
\* evidence: test source/raft_test.go:3517 TestLeaderTransferIgnoreProposal "should return drop proposal error while transferring" -> drop while a transfer is pending
\* evidence: impl source/raft.go:969 "drop any new proposals."
\* evidence: impl source/raft.go:962 "case pb.MsgProp:"
\* watch:    raft.go:stepLeader (MsgProp); raft.go:stepFollower (MsgProp); raft.go:stepCandidate (MsgProp); raft.go:increaseUncommittedSize; node.go:run (propc)
\* verified: V00
\* note:     the decision function lives in ExpectedDecision; each drop branch is documented but the precedence, the follower-without-leader drop and "Accepted otherwise" are code-only, and README.md:170 says "There is no guarantee that a proposed command will be committed" (removed as an evidence line: it supports no part of the intent). raft.go:969 is retyped to impl (narration); the removed-leader drop is backed by history db2dbe524.
\* clause drop branches (removed, transfer, quota, candidate, forwarding disabled): requirement — raft.go:71,163,199, history db2dbe524, doc.go:224, tests above
\* clause Forwarded at a follower with a leader and forwarding enabled: requirement — test TestDisableProposalForwarding (r2 forwards)
\* clause follower-without-leader drop, branch precedence and Accepted otherwise: impl-abstraction — raft.go:962-994, 1199-1201, 1235-1244 only
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement); handle clause by clause
\* review:   status impl-abstraction -> requirement by narrowing intent to the documented drop and forward cases (precedence and Accepted-otherwise stay impl-abstraction clauses), retyped raft.go:969 to impl, added history db2dbe524, removed README.md:170 which supports no part of the intent.
OutcomeSoundness == \A o\in history.outcomes:o.decision=ExpectedDecision(o)
\* Actual completed reads, not ReadState production. Prefix history is a symbolic SM.
\* REQ-EVIDENCE ReadBasis
\* intent:   every completed read used a read index confirmed in the leader's own term by a quorum of a configuration the cluster actually had, after the leader committed an entry of its term (except for a single-voter leader), and its state at that index includes every write completed before the read was invoked.
\* status:   mixed
\* evidence: comment source/raft.go:48 "ReadOnlySafe guarantees the linearizability of the read only request by" -> quorum confirmation; completed writes visible (linearizability)
\* evidence: history f9382a4d7 (raft: fix read index request for #7331) "raft: fix read index request for #7331" -> the committed-in-term check was added as a bug fix, i.e. intended
\* evidence: test source/raft_test.go:2317 TestReadOnlyForNewLeader "a leader only accepts MsgReadIndex message" -> leader committed an entry of its term before serving a read
\* evidence: doc source/README.md:28 "leader checks with quorum and bypasses Raft log before processing read-only queries" -> quorum confirmation in the leader's term
\* evidence: comment source/node.go:170 "any linearizable read requests issued before the read request can be" -> writes completed before the read are visible
\* evidence: impl source/raft.go:1000 "Reject read only request when this leader has not committed any log entry"
\* evidence: impl source/raft.go:1109 "if r.prs.Voters.VoteResult(r.readOnly.recvAck(m.From, m.Context)) != quorum.VoteWon {"
\* watch:    raft.go:stepLeader (MsgReadIndex, MsgHeartbeatResp); read_only.go:addRequest; read_only.go:recvAck; read_only.go:advance; raft.go:bcastHeartbeatWithCtx; raft.go:reset
\* verified: V00
\* note:     only ReadOnlySafe is modelled. raft.go:1000 is retyped to impl (it narrates the following check); the history line now quotes the commit message instead of that comment. Mixed origins, not splittable (one LET); per-clause status below.
\* clause quorum confirmation in the read's term: requirement — raft.go:48-49, README.md:28
\* clause leader belongs to the confirming voter set, and that set is nonempty: unknown — no non-impl evidence (cf. QuorumAccounting)
\* clause leader committed in its term: requirement — test TestReadOnlyForNewLeader, history f9382a4d7
\* clause singleton exemption: impl-abstraction — raft.go:996-997 "If more than the local vote is needed" (an optimization), raft.go:1021-1026
\* clause confirming configuration is a real (applied) configuration: requirement — README.md:193 (configuration changes take effect when applied)
\* clause writes completed before invocation are visible: requirement — node.go:168-171, README.md:27
\* relabel:  requirement -> mixed (clause statuses: impl-abstraction, requirement, unknown); handle clause by clause
\* review:   narrowed intent (singleton exemption explicit; leader-in-voters and nonempty set moved to an unknown clause), retyped raft.go:1000 to impl as narration, re-quoted f9382a4d7 to its commit message, added "->" suffixes.
ReadBasis == \A x\in history.readResults:
    LET r==x.rd IN
    /\ r.leader\in r.confirmConfig.voters
    /\ r.confirmConfig.voters#{}
    /\ Won(r.confirmConfig.voters,r.confirmAcks)
    /\ r.confirmConfig=ConfigOf(r.hist) \/
         \E c\in history.applied:r.confirmConfig=ConfigOf(c) /\ Covers(c,r.hist)
    /\ r.confirmTerm=r.term
    /\ r.singleton \/ (r.index>0 /\ r.hist[r.index].term=r.term)
    /\ \A h\in x.beforeWrites:Covers(Prefix(x.app,r.index),h)
\* REQ-EVIDENCE ReadApplication
\* intent:   a read completes only once the reader's applied state contains the read's log prefix and has reached the read index.
\* status:   requirement
\* evidence: comment source/node.go:64 "when its applied index is greater than the index in ReadState." -> read served only after applied state reaches the read index
\* evidence: comment source/node.go:169 "Once the application advances further than the read" -> read served only after applied state reaches the read index
\* evidence: comment source/rawnode.go:277 "Once the application advances further than the read" -> same rule for RawNode
\* watch:    node.go:Ready (ReadStates contract); node.go:ReadIndex; rawnode.go:ReadIndex; read_only.go:ReadState
\* verified: V00
\* note:     the fence is enforced by the caller (base.tla ProtocolCompleteRead), not by raft. The docs say "greater than" while the property and ReadFence="Inclusive" accept equality; see out/concerns.md. The prefix (Covers) part follows from the fence plus AppliedAgreement rather than from a separate statement. read_only.go:20 was removed: it says the caller must call ReadIndex first, not when the read may complete.
\* review:   removed read_only.go:20, which does not support the fence; added "->" suffixes.
ReadApplication == \A x\in history.readResults:
    Covers(x.app,x.rd.hist) /\ Len(x.app)>=x.rd.index
\* REQ-EVIDENCE ReadCorrelation
\* intent:   a completed read uses a ReadState that carries the request's own context and was produced for that very request, and the request was actually handed to raft.
\* status:   requirement
\* evidence: comment source/read_only.go:21 "it's also caller's duty to differentiate if this" -> the ReadState used carries the request's own context
\* evidence: comment source/node.go:66 "The returned is only valid for the request that requested to read." -> the ReadState was produced for that very request
\* evidence: comment source/node.go:171 "The read state will have the same rctx attached." -> the ReadState carries the request's own context
\* evidence: test source/node_test.go:164 TestNodeReadIndex "It also ensures that ReadState can be read out through ready chan." -> ReadState with the request's context is delivered
\* evidence: impl source/raft.go:1117 "r.readStates = append(r.readStates, ReadState{Index: rs.index, RequestCtx: req.Entries[0].Data})"
\* watch:    read_only.go:addRequest; read_only.go:advance; raft.go:stepLeader (MsgHeartbeatResp, MsgReadIndex); raft.go:stepFollower (MsgReadIndexResp)
\* verified: V00
\* note:     rd.rid and requests[].handoff are model ghost witnesses; empty contexts are only allowed when AllowEmptyContext=TRUE.
\* review:   ok
ReadCorrelation == \A x\in history.readResults:
    x.rd.id=x.context /\ x.rd.rid=x.id /\ requests[x.id].handoff
\* REQ-EVIDENCE NoUnexpectedFatal
\* intent:   no node reaches a fatal path whose trigger is documented as forbidden: applied beyond committed, commit beyond the last index, overwriting committed entries, or removing an untracked peer.
\* status:   mixed
\* evidence: comment source/log.go:37 "Invariant: applied <= committed" -> no appliedTo-bounds fatal
\* evidence: comment source/raft.go:513 "The leader MUST NOT forward the follower's commit to" -> no commit-beyond-lastIndex fatal
\* evidence: comment source/tracker/tracker.go:142 "RemoveAny removes this peer, which *must* be tracked as a voter or learner," -> no remove-unknown-peer fatal
\* evidence: impl source/log.go:203 "Was the raft log corrupted, truncated, or lost?"
\* watch:    log.go:commitTo; log.go:appliedTo; log.go:append; log.go:maybeAppend; raft.go:Step (MsgHup slice); raft.go:maybeSendAppend; raft.go:loadState; tracker/tracker.go:RemoveAny; storage.go:Append; storage.go:CreateSnapshot
\* verified: V00
\* note:     searched README.md, doc.go and design.md for a general "must not panic" statement and found none. Each Fatal reason mirrors a Panicf; only some reasons have a comment saying the condition must not occur. Removed storage.go:214 (it forbids compacting beyond applied, which is not a modelled fatal) and raft.go:665 (a TODO about removing the leader-to-candidate panic, not a rule; its clause stays unknown). storage.go:237 has only a TODO "ensure the entries are continuous".
\* clause appliedTo bounds, commit beyond lastIndex: requirement — log.go:37, raft.go:513-514
\* clause append below committed, conflict with committed entry: requirement — Raft-paper §5.4.3 (committed entries are never replaced; see CommittedHistory)
\* clause remove unknown peer: requirement — caller contract tracker/tracker.go:142
\* clause Storage.Append gap, CreateSnapshot beyond lastIndex: unknown — only Panicf and TODO storage.go:237; no stated contract
\* clause follower-to-leader / leader-to-candidate, need non-empty snapshot, Hup slice compacted, append next out of bounds, leader missing self progress, empty proposal: unknown — impl Panicf only
\* relabel:  requirement -> mixed (clause statuses: requirement, unknown); handle clause by clause
\* review:   status unknown -> requirement by narrowing intent to the fatal paths with documented forbidden triggers (others recorded as unknown clauses); removed storage.go:214 (wrong condition) and raft.go:665 (TODO, no rule); corrected the clause sources.
NoUnexpectedFatal == \A n\in Server:raft[n].fatal=""

\* Structural assertions: do not disguise finite exploration limits as TypeOK.
\* REQ-EVIDENCE TypeOK
\* intent:   all state variables have their expected shapes and value ranges.
\* status:   mixed
\* evidence: comment source/tracker/tracker.go:30 "Invariant: Learners and Voters does not intersect" -> clause voters\cap learners = {} only
\* evidence: impl source/tracker/tracker.go:156 "} else if okV && okL {"
\* watch:    tracker/tracker.go:InitProgress; tracker/tracker.go:RemoveAny; raft.go:applyConfChange; raft.go:restore
\* verified: V00
\* note:     type/shape check of the model; not splittable at top level without separating the per-node conjunction. One clause carries a real requirement.
\* clause voters\cap learners = {}: requirement — comment tracker/tracker.go:30
\* clause remaining domain/range checks: model-internal — model well-formedness
\* relabel:  model-internal -> mixed (clause statuses: model-internal, requirement); handle clause by clause
\* review:   ok
TypeOK ==
    /\ DOMAIN raft=Server /\ DOMAIN disk=Server /\ DOMAIN ready=Server
    /\ DOMAIN application=Server /\ DOMAIN requests=RequestId
    /\ \A n\in Server:
       /\ raft[n].role\in {"Follower","PreCandidate","Candidate","Leader"}
       /\ raft[n].term\in Nat /\ raft[n].vote\in Server\cup {0}
       /\ raft[n].lead\in Server\cup {0} /\ raft[n].commit\in Nat /\ raft[n].applied\in Nat
       /\ raft[n].config.voters\subseteq Server /\ raft[n].config.learners\subseteq Server
       /\ raft[n].config.voters\cap raft[n].config.learners={}
       /\ DOMAIN raft[n].prs=Members(raft[n])
       /\ raft[n].uoff>=1
       /\ \A p\in Members(raft[n]):raft[n].prs[p].mode\in {"Probe","Replicate","Snapshot"}
    /\ IsABag(wire)
\* REQ-EVIDENCE LogStructure_CommitBounds
\* intent:   on every node the applied index never exceeds the commit index, which never exceeds the last log index.
\* status:   requirement
\* evidence: comment source/log.go:37 "Invariant: applied <= committed" -> applied index never exceeds the commit index
\* evidence: comment source/raft.go:513 "The leader MUST NOT forward the follower's commit to" -> commit index never exceeds the last log index
\* evidence: test source/log_test.go:451 TestCommitTo "commit out of range -> panic" -> commit beyond the last index is treated as an error
\* evidence: impl source/log.go:202 "if l.lastIndex() < tocommit {"
\* watch:    log.go:commitTo; log.go:appliedTo; log.go:maybeAppend; raft.go:sendHeartbeat; raft.go:handleHeartbeat; raft.go:loadState
\* verified: V00
\* note:     split from LogStructure (clauses 1-2). History a90ffa34e was removed as evidence: its message only explains a better panic message.
\* review:   removed history a90ffa34e, whose message ("Give a human being some insight...") explains a panic message and states no rule; added "->" suffixes.
LogStructure_CommitBounds == \A n\in Server:
    /\ raft[n].applied<=raft[n].commit
    /\ raft[n].commit<=Last(raft[n])
\* REQ-EVIDENCE LogStructure_Indexing
\* intent:   every log entry sits at the position equal to its index, and the unstable segment ends within the log.
\* status:   model-internal
\* evidence: comment source/log_unstable.go:19 "unstable.entries[i] has raft log position i+unstable.offset." -> unstable segment positions (analogue in the code representation)
\* watch:    log_unstable.go:truncateAndAppend; log_unstable.go:stableTo; log_unstable.go:restore; raft.go:appendEntry
\* verified: V00
\* note:     split from LogStructure (clauses 3-4); well-formedness of the model's Hist/unstable representation.
\* review:   ok
LogStructure_Indexing == \A n\in Server:
    /\ \A k\in DOMAIN Hist(raft[n]):Hist(raft[n])[k].index=k
    /\ raft[n].uoff+Len(raft[n].unstable)<=Last(raft[n])+1

\* REQ-EVIDENCE LogStructure
\* intent:   conjunction of the parts below; kept so existing configs and references still work
\* status:   model-internal
\* verified: V00
\* note:     split by origin into LogStructure_CommitBounds (requirement), LogStructure_Indexing (model-internal)
\* review:   ok
LogStructure == LogStructure_CommitBounds /\ LogStructure_Indexing

\* Public reference actions: identical protocol relation, total observer update.
Tick(n,timeout) == ProtocolTick(n,timeout) /\ quality'=QualityEvent("Tick",[node |-> n])
Campaign(n,timeout) == ProtocolCampaign(n,timeout) /\ quality'=QualityEvent("Campaign",[node |-> n])
TickQuiesced(n) == ProtocolTickQuiesced(n) /\ quality'=QualityEvent("TickQuiesced",[unused |-> 0])
TransferLeader(n,target,timeout) == ProtocolTransferLeader(n,target,timeout) /\ quality'=QualityEvent("TransferLeader",[node |-> n,target |-> target])
Invoke(n,id,kind,target,w,z,parent,ctx) == ProtocolInvoke(n,id,kind,target,w,z,parent,ctx) /\ quality'=QualityEvent("Invoke",[unused |-> 0])
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
ClientActions == \E n\in Server,id\in RequestId,kind\in Kinds\cup {"Read"},
     target\in Server\cup {0},w\in PayloadWeights,z\in EncodedWeights,parent\in RequestId\cup {0}:
     \E ctx\in {id,0}: Invoke(n,id,kind,target,w,z,parent,ctx)
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
