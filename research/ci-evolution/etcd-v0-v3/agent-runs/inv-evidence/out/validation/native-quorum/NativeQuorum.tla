----------- MODULE NativeQuorum -----------
EXTENDS base, Json
VARIABLE marker
H0 == INSTANCE HistoricalV00
FlatR == [H0!InitialRaft(1,10) EXCEPT !.role="Leader",!.lead=1,!.term=2,
 !.config=[voters |-> {1,2,3},learners |-> {}],!.commit=1,!.applied=1,
 !.store=H0!Store(<<H0!Entry(2,1,"Normal",0,0,0,8),H0!Entry(2,2,"Normal",0,0,1,9)>>,H0!EmptySnapshot,0,H0!EmptyHS),!.uoff=3,
 !.prs=[n\in {1,2,3} |-> H0!Progress(IF n=1 THEN 2 ELSE 1,3,TRUE)]]
FlatPost == H0!Step(FlatR,[H0!Message("MsgAppResp",2,1,2) EXCEPT !.index=2],10)
JointR == [InitialRaft(1,10) EXCEPT !.role="Leader",!.lead=1,!.term=2,
 !.config=[EmptyConfig EXCEPT !.voters={1,2},!.outgoing={2,3}],!.commit=1,!.applied=1,
 !.store=Store(<<Entry(2,1,"Normal",0,0,0,8),Entry(2,2,"Normal",0,0,1,9)>>,EmptySnapshot,0,EmptyHS),!.uoff=3,
 !.prs=[n\in {1,2,3} |-> Progress(IF n=1 THEN 2 ELSE 1,3,TRUE)]]
JointPost == Step(JointR,[Message("MsgAppResp",2,1,2) EXCEPT !.index=2],10)
JointEnough == Step([JointR EXCEPT !.prs[3].match=2],[Message("MsgAppResp",2,1,2) EXCEPT !.index=2],10)

OldQ == LET H==INSTANCE HistoricalV00 WITH history <- [H0!EmptyHistory EXCEPT !.commitUses=FlatPost.commitUses] IN H!QuorumAccounting
NewQ == LET H==INSTANCE base WITH history <- [EmptyHistory EXCEPT !.commitUses=JointEnough.commitUses] IN H!QuorumAccounting
InitWitness == /\ marker=0 /\ raft=EmptyFunction /\ disk=EmptyFunction /\ ready=EmptyFunction
 /\ application=EmptyFunction /\ requests=EmptyFunction /\ wire=EmptyBag /\ history=EmptyHistory /\ quality=EmptyQuality
NextWitness == marker'=marker /\ FALSE
Check == /\ Assert(FlatPost.commit=2 /\ JointPost.commit=1 /\ JointEnough.commit=2,"quorum outcomes")
 /\ Assert(FlatPost.commitUses#{} /\ JointEnough.commitUses#{} /\ OldQ /\ NewQ,"nonempty original commit contract")
 /\ JsonSerialize("native-results.json",[oldModel |-> [commit |-> FlatPost.commit,commitUses |-> FlatPost.commitUses,invariant |-> OldQ],
 newModelInsufficient |-> [commit |-> JointPost.commit,commitUses |-> JointPost.commitUses,invariant |-> "no commit event; not vacuous pass"],
 newModelSufficient |-> [commit |-> JointEnough.commit,commitUses |-> JointEnough.commitUses,invariant |-> NewQ],
 oldCode |-> "unsupported native V00 binding; joint state not representable",newCode |-> "replay-V01-observed-07 joint-quorum-insufficient/sufficient"])
============================
