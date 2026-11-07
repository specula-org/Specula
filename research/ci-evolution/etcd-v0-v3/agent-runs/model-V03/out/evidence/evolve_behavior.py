from pathlib import Path
p=Path('out/repaired-spec/base.tla');s=p.read_text()
a=s.index('Category A.');b=s.index('Core functions below',a)
s=s[:a]+'''Category A. Supplied V03 source, adjacent to supplied V02.
Source references use /workspace/new/source; update.patch is the version delta.
The inherited V02 predicates are preserved for the following property phase.
'''+s[b:]
a=s.index('\\* Empty ConfChangeV2 marshals');b=s.index('BootLog ==',a)
s=s[:a]+'''\\* V03 raft.go:advance: automatic leave uses nil Data, zero payload bytes.
\\* It has the same Entry encoding size as the empty leader entry.
AutoLeaveWeight == 0
AutoLeaveEncoded == EmptyEncoded
'''+s[b:]
s=s.replace('IF r.quota>0 /\\ r.quota+Weight(es)>MaxUncommitted','IF r.quota>0 /\\ Weight(es)>0 /\\ r.quota+Weight(es)>MaxUncommitted')
s=s.replace('Progress(IF n=r.id THEN s.index ELSE 0,s.index+1,TRUE)', 'Progress(IF n=r.id THEN s.index-1 ELSE 0,s.index,TRUE)')
s=s.replace('\\* raft.go:999-1030; both legacy and V2 entries share pending-conf admission.', '''\\* V03 raft.go:stepLeader MsgProp (1035-1075): phase admission is based on
\\* len(AsV2().Changes), not LeaveJoint(). Empty explicit transitions therefore
\\* pass this gate in joint state, then panic if the caller applies them.
\\* UPDATE-MAP code: raft.go:stepLeader; Update!AffectedConfigurationActions''')
s=s.replace('ELSE IF r.pendingConf>r.applied THEN\n        RewriteConf', '''ELSE IF r.pendingConf>r.applied \\/
            (r.config.outgoing#{} /\\ es[k].changes# <<>>) \\/
            (r.config.outgoing={} /\\ es[k].changes= <<>>) THEN
        RewriteConf''')
s=s.replace('Progress(0,Last(r)+1,TRUE)', 'Progress(0,Last(r),TRUE)')
s=s.replace('c==IF b.commit>a.commit THEN BcastAppend(b) ELSE b\n       IN IF c.transfer#0 /\\ c.transfer\\notin members', 'c==IF b.commit>a.commit THEN BcastAppend(b) ELSE ProbeConfig(b,Members(b))\n       IN IF c.transfer#0 /\\ c.transfer\\notin VoterIDs(cfg)')
# Iteration deliberately includes self, like prs.Visit in switchToConfig.
i=s.index('ApplyConfCore(r,e,timeout) ==')
s=s[:i]+'''\\* V03 switchToConfig probes every Progress, including self. Paused and
\\* compacted/empty paths are delegated to the unchanged MaybeSendAppend.
RECURSIVE ProbeConfig(_, _)
ProbeConfig(r,peers) == IF peers={} \\/ r.fatal#"" THEN r ELSE
 LET n==MinSet(peers) IN ProbeConfig(MaybeSendAppend(r,n,FALSE),peers\\{n})
'''+s[i:]
s=s.replace('Progress(0,Len(h)+1,TRUE)', 'Progress(0,Len(h),TRUE)')
a=s.index('AdvanceCore(r,b,n) ==');b=s.index('ProtocolAdvance(n) ==',a)
s=s[:a]+'''AdvanceCore(r,b,n) ==
    LET reduced==[r EXCEPT !.quota=Max(0,@-Weight(b.committed))]
        a==AppliedTo(reduced,b.cursor)
        leave==V2Entry(0,0,0,<<>>,"Auto",AutoLeaveWeight,AutoLeaveEncoded)
        auto==a.fatal="" /\\ b.cursor>0 /\\ a.config.autoLeave /\\
              r.applied<r.pendingConf /\\ b.cursor>=r.pendingConf /\\ a.role="Leader"
        b0==IF auto THEN AppendEntry(a,<<leave>>) ELSE a
        b1==IF ~auto THEN b0 ELSE IF b0.decision="DropQuota"
            THEN Fatal(b0,"refused un-refusable auto-leaving ConfChangeV2")
            ELSE [b0 EXCEPT !.pendingConf=Last(b0)]
        last==IF b.entries= <<>> THEN MissingEntry(0) ELSE b.entries[Len(b.entries)]
        stable==b.entries# <<>> /\\ last.index>=b1.uoff /\\ last.index<=Last(b1) /\\
                 Term(b1,last.index)=last.term
    IN IF b1.fatal#"" THEN b1 ELSE [b1 EXCEPT
        !.unstable=IF stable THEN Suffix(@,last.index+2-r.uoff) ELSE @,
        !.uoff=IF stable THEN last.index+1 ELSE @,
        !.usnap=IF b.snapshot.index>0 /\\ r.usnap.index=b.snapshot.index THEN EmptySnapshot ELSE @,
        !.prevHS=b.hs]
'''+s[b:]
# Preserve eligible's old meaning; append raw new evidence rather than redefining it.
s=s.replace('beforeLast |-> Last(r), afterHist |-> Hist(a), pending |-> a.pendingConf,', '''oldApplied |-> r.applied, cursor |-> b.cursor, pendingBefore |-> r.pendingConf,
              crossingEligible |-> r.config.autoLeave /\\ b.cursor>0 /\\
                  r.applied<r.pendingConf /\\ b.cursor>=r.pendingConf /\\ r.role="Leader",
              quotaBefore |-> r.quota, committedWeight |-> Weight(b.committed), quotaAfter |-> a.quota,
              beforeLast |-> Last(r), afterHist |-> Hist(a), pending |-> a.pendingConf,''')
# Proposal observation adds phase information while keeping all existing fields.
s=s.replace('[node |-> r.id, role |-> r.role, voters |-> VoterIDs(r.config), learners |-> r.config.learners,', '[node |-> r.id, role |-> r.role, config |-> r.config, voters |-> VoterIDs(r.config), learners |-> r.config.learners,')
# Constructor's temporary progress changes, then Reset intentionally overwrites it.
s=s.replace('Progress(0,1,FALSE)]]', 'Progress(0,Len(h),TRUE)]]')
p.write_text(s)
