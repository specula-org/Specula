-------------------------- MODULE ActionCampaign --------------------------
EXTENDS base, Json
CONSTANTS AVFromFile, AVInputPath
VARIABLE avCase

\* Independent bounded input enumeration, not a claim of protocol reachability.
AVDomain == [kind : {"Normal","AddVoter","V2"}, applied : {3,4}, pre_vote : BOOLEAN, learner : BOOLEAN]
AVInputs == IF AVFromFile THEN SeqSet(JsonDeserialize(AVInputPath)) ELSE AVDomain

\* Setup maps a concrete MemoryStorage snapshot at index 3 plus one entry.
\* BootLog below the snapshot is an ignored prefix for this operation.
AVBefore(c) ==
    LET cfg == [BootConfig EXCEPT !.voters=IF c.learner THEN {2,3} ELSE {1,2,3},
                                 !.learners=IF c.learner THEN {1} ELSE {}]
        h == Append(BootLog,IF c.kind="V2" THEN V2Entry(1,4,0,<<Change("AddVoter",3)>>,"Auto",0,1) ELSE Entry(1,4,c.kind,0,3,0,1))
        snap == [index |-> 3, term |-> 1, hist |-> BootLog, config |-> cfg]
    IN [InitialRaft(1,3) EXCEPT !.config=cfg,
        !.store=Store(h,snap,3,[term |-> 1,vote |-> 0,commit |-> 4]),
        !.unstable= <<>>, !.uoff=5, !.commit=4, !.applied=c.applied,
        !.prs=[p\in {1,2,3} |-> Progress(0,5,TRUE)], !.preVote=c.pre_vote]

AVProjection(r) ==
    [role |-> r.role, term |-> r.term, vote |-> r.vote, lead |-> r.lead,
     applied |-> r.applied, commit |-> r.commit, last |-> Last(r),
     messages |-> {[type |-> m.type, from |-> m.from, to |-> m.to,
                   term |-> m.term, index |-> m.index, logTerm |-> m.logTerm]:m\in DOMAIN r.out}]
AVRecord(c) == [action |-> "StepHup",input |-> c,output |-> AVProjection(StepHup(AVBefore(c),3))]
AVInit == /\ Init
          /\ \A n\in Server:raft[n].timeout=ElectionTick
          /\ avCase\in AVInputs
          /\ PrintT("AV_RESULT " \o ToJson(AVRecord(avCase)))
AVNext == UNCHANGED <<vars,avCase>>
=============================================================================
