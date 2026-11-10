----------------------- MODULE SourceAlignmentChecks -----------------------
EXTENDS base

\* White-box reference regression fixtures, not implementation executions or
\* reachable protocol counterexamples. They test source API result precedence.
\* raft.go:454-457 returns on empty refill before snapshot lookup;
\* log.go:170-174 selects an unstable snapshot without consulting Storage.
AlignmentNext == UNCHANGED vars
SourceAlignment ==
    LET n == BootPeers[1]
        peer == BootPeers[2]
        h == BootLog
        snap == [index |-> Len(h), term |-> h[Len(h)].term,
                 hist |-> h, config |-> BootConfig]
        r == [InitialRaft(n,ElectionTick) EXCEPT
               !.role="Leader", !.unstable= <<>>, !.uoff=Len(h)+1,
               !.store=Store(h,snap,Len(h),EmptyHS),
               !.prs[peer]=Progress(0,1,TRUE)]
        unavailable == [r EXCEPT !.snapAvailable=FALSE]
        unstable == [unavailable EXCEPT !.usnap=snap]
        sent == MaybeSendAppend(unstable,peer,TRUE)
        inactive == [r EXCEPT !.prs[peer].active=FALSE]
    IN /\ MaybeSendAppend(r,peer,FALSE)=r
       /\ MaybeSendAppend(unavailable,peer,TRUE)=unavailable
       /\ MaybeSendAppend(inactive,peer,TRUE)=inactive
       /\ BagCardinality(sent.out)=1
       /\ sent.prs[peer].mode="Snapshot"
       /\ sent.prs[peer].pending=snap.index
       /\ Hist(sent)=Hist(unstable)
       /\ \A m\in DOMAIN sent.out:
             m.type="MsgSnap" /\ m.from=n /\ m.to=peer /\ m.snapshot=snap
=============================================================================
