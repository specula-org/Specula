from pathlib import Path
import json,re,shutil,hashlib,time
R=Path('/workspace'); O=R/'out/validation'
# Original sources, specs and frozen decisions are immutable inputs.
inputs=[p for d in ['versions','decisions','coordinator-property-pilot'] for p in (R/d).rglob('*') if p.is_file() and p.name!='action_validation_test.go']
if not (O/'input-hashes.json').exists():
 (O/'input-hashes.json').write_text(json.dumps({str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},indent=2))
 (O/'started.json').write_text(json.dumps({'epoch':time.time()}))
def op(text,name,nextname):return text[text.index(name+'(') if name+'(' in text else text.index(name+' =='):text.index(nextname+'(') if nextname+'(' in text else text.index(nextname+' ==')]
common=r'''
VARIABLE audit
EmptyAudit == [advances |-> {}, ready |-> {}, proposals |-> {}, switches |-> {}]
AdvanceObservation(r,b,a) == [before |-> Hist(r), after |-> Hist(a),
 oldSnap |-> r.usnap.index,batchSnap |-> b.snapshot.index,afterSnap |-> a.usnap.index,
 cursor |-> b.cursor,applied |-> a.applied,oldApplied |-> r.applied,
 config |-> r.config,role |-> r.role,term |-> r.term,pendingBefore |-> r.pendingConf,
 pendingAfter |-> a.pendingConf,quotaBefore |-> r.quota,quotaAfter |-> a.quota,
 committedWeight |-> Weight(b.committed),fatal |-> a.fatal,decision |-> a.decision,raw |-> r.id\in RawNodes,
 outBefore |-> r.out,outAfter |-> a.out,readsBefore |-> r.readStates,readsAfter |-> a.readStates,
 ssBefore |-> r.prevSS,ssAfter |-> a.prevSS,batchReads |-> b.reads,
 hsBefore |-> r.prevHS,hsAfter |-> a.prevHS,batchHS |-> b.hs]
ReadyObservation(r,b,a) == [raw |-> r.id\in RawNodes,
 outBefore |-> r.out,outAfter |-> a.out,readsBefore |-> r.readStates,readsAfter |-> a.readStates,
 quotaBefore |-> r.quota,quotaAfter |-> a.quota,batch |-> b,
 ssBefore |-> r.prevSS,ssAfter |-> a.prevSS,hsBefore |-> r.prevHS,hsAfter |-> a.prevHS,
 appliedBefore |-> r.applied,appliedAfter |-> a.applied,
 unstableBefore |-> r.unstable,unstableAfter |-> a.unstable]
RevisedProposalObservation(r,es,a,qs) == ProposalObservation(r,es,a,qs) @@
 [config |-> r.config,beforeTerm |-> r.term,afterPending |-> a.pendingConf]
SwitchObservation(r,a) == [node |-> r.id,role |-> r.role,before |-> r.config,
 after |-> a.config,oldTransfer |-> r.transfer,afterTransfer |-> a.transfer,fatal |-> a.fatal]
\* These observers consume real pre/post states, never decide protocol behavior.
AuditNext == [
 advances |-> {AdvanceObservation(raft[n],ready[n],raft'[n]):
   n\in {i\in Server:ProtocolAdvance(i)}},
 ready |-> {ReadyObservation(raft[n],ready'[n],raft'[n]):
   n\in {i\in Server:ProtocolReady(i)}},
 proposals |-> {o @@ [config |-> raft[o.node].config,beforeTerm |-> raft[o.node].term,
   afterPending |-> raft'[o.node].pendingConf]:o\in quality'.proposals},
 switches |-> {SwitchObservation(raft[o.node],raft'[o.node]):o\in quality'.effects}]
MaintainedInit == Init /\ audit=EmptyAudit
MaintainedNext == Next /\ audit'=AuditNext
maintainedVars == <<vars,audit>>
MaintainedSpec == MaintainedInit /\ [][MaintainedNext]_maintainedVars
RevisedCampaignDecisionEligibility == \A o\in quality.campaigns:RevisedCampaignContract(o)
ActualBootstrap(e,k) == k\in DOMAIN BootLog /\ e=BootLog[k]
RevisedConfigurationTransitionSafety == \A c\in history.commitUses:
 \A k\in (c.oldCommit+1)..Len(c.hist):
  (c.hist[k].kind\in ConfKinds /\ ~ActualBootstrap(c.hist[k],k)) =>
   c.config=ConfigOf(Prefix(c.hist,k-1))
CanonicalLeave(e,a,w,z) == e=V2Entry(a.term,Len(a.before)+1,0,<<>>,"Auto",w,z)
AdvanceEnvelope(a) ==
 /\ (a.oldSnap#0 /\ a.oldSnap#a.batchSnap => a.afterSnap=a.oldSnap)
 /\ (a.cursor#0 => a.applied=a.cursor)
RevisedAckPreservation == \A a\in audit.advances:
 AdvanceEnvelope(a) /\ RevisedAutoLeaveContract(a) /\
 (a.after#a.before => ~\E k\in (a.oldApplied+1)..Len(a.before):IsLeave(a.before[k]) /\ a.before[k].id=0)
RevisedAutoLeaveAdvance == \A a\in audit.advances:RevisedAutoLeaveContract(a)
'''
# Forward operator references aren't permitted in TLA: insert contracts before their uses.
common_end=common[common.index('RevisedAckPreservation'):];common=common[:common.index('RevisedAckPreservation')]
auto12=r'''
RevisedAutoLeaveContract(a) ==
 LET eligible==a.config.autoLeave /\ a.role="Leader" /\ a.cursor>0 /\ a.cursor>=a.pendingBefore
     blocked==a.quotaBefore>0 /\ a.quotaBefore+AutoLeaveWeight>MaxUncommitted
 IN /\ a.fatal=""
    /\ IF ~eligible THEN a.after=a.before /\ a.pendingAfter=a.pendingBefore
       ELSE IF blocked THEN a.after=a.before /\ a.pendingAfter=Len(a.before)
       ELSE /\ a.after=Append(a.before,V2Entry(a.term,Len(a.before)+1,0,<<>>,"Auto",AutoLeaveWeight,AutoLeaveEncoded))
    /\ a.quotaAfter=Max(0,a.quotaBefore+(IF eligible /\ ~blocked THEN AutoLeaveWeight ELSE 0)-a.committedWeight)
'''
auto3=r'''
RevisedAutoLeaveContract(a) ==
 LET trigger==a.config.autoLeave /\ a.role="Leader" /\ a.cursor>0 /\
              a.oldApplied<a.pendingBefore /\ a.pendingBefore<=a.cursor
 IN /\ a.fatal=""
    /\ IF trigger THEN
         /\ a.after=Append(a.before,V2Entry(a.term,Len(a.before)+1,0,<<>>,"Auto",0,AutoLeaveEncoded))
         /\ a.pendingAfter=Len(a.before)+1
       ELSE a.after=a.before /\ a.pendingAfter=a.pendingBefore
    /\ a.quotaAfter=Max(0,a.quotaBefore-a.committedWeight)
'''
ready=r'''
RevisedReadyContract(o) ==
 /\ o.quotaAfter=o.quotaBefore
 /\ o.batch.messages=o.outBefore /\ o.batch.reads=o.readsBefore
 /\ o.outAfter=EmptyBag /\ o.readsAfter=<<>>
 /\ o.ssAfter=o.batch.ss
 /\ o.hsAfter=o.hsBefore /\ o.appliedAfter=o.appliedBefore
 /\ o.unstableAfter=o.unstableBefore
RevisedReadyOwnership == \A o\in audit.ready:RevisedReadyContract(o)
PendingOutputContract(a) == a.outAfter=a.outBefore /\ a.readsAfter=a.readsBefore /\ a.ssAfter=a.ssBefore
AdvancePreservesPendingOutput == \A a\in audit.advances:PendingOutputContract(a)
\* Same original pagination/cursor predicate, supplied ACTUAL lost observations.
ActualLostReads == {a\in audit.advances:a.readsBefore#a.readsAfter}
RevisedReadyAccounting ==
 LET H==INSTANCE base WITH history <- [history EXCEPT !.lostReads=ActualLostReads]
 IN H!ReadyAccounting
'''
proposal=r'''
\* Independent content oracle: never calls protocol RewriteConf.
ContractLeave(e) == e.kind="V2" /\ e.changes=<<>> /\ e.transition="Auto"
RECURSIVE ContractBatch(_,_,_,_,_)
ContractBatch(es,c,p,applied,last) ==
 IF es=<<>> THEN [entries |-> <<>>,pending |-> p] ELSE
 LET e==Head(es)
     refuse==e.kind\in ConfKinds /\ (p>applied \/
       (c.outgoing#{} /\ ~ContractLeave(e)) \/ (c.outgoing={} /\ ContractLeave(e)))
     effective==IF refuse THEN Entry(0,0,"Normal",0,0,0,EmptyEncoded) ELSE e
     nextPending==IF e.kind\in ConfKinds /\ ~refuse THEN last+1 ELSE p
     rest==ContractBatch(Tail(es),c,nextPending,applied,last+1)
 IN [entries |-> <<effective>>\o rest.entries,pending |-> rest.pending]
RevisedExpectedDecision(o) ==
 IF o.role="Leader" THEN
  IF ~o.member THEN "DropRemoved" ELSE IF o.transfer#0 THEN "DropTransfer"
  ELSE IF o.quota>0 /\ o.weight>0 /\ o.quota+o.weight>MaxUncommitted THEN "DropQuota" ELSE "Accepted"
 ELSE IF o.role#"Follower" \/ o.lead=0 THEN "DropNoLeader"
 ELSE IF ~o.forwarding THEN "DropForwardDisabled" ELSE "Forwarded"
ProposalOutcome(o) ==
 LET b==ContractBatch(o.entries,o.config,o.pending,o.applied,Len(o.before))
 IN [role |-> o.role,member |-> o.node\in o.voters\cup o.learners,
 transfer |-> o.transfer,quota |-> o.quota,weight |-> Weight(b.entries),
 lead |-> o.lead,forwarding |-> ~o.noForward,decision |-> o.decision]
RevisedProposalContract(o) ==
 LET b==ContractBatch(o.entries,o.config,o.pending,o.applied,Len(o.before))
     expected==RevisedExpectedDecision(ProposalOutcome(o))
     assigned==[k\in DOMAIN b.entries |-> [b.entries[k] EXCEPT !.term=o.beforeTerm,!.index=Len(o.before)+k]]
 IN /\ o.entries#<<>> /\ o.decision=expected
    /\ IF expected="Accepted" THEN
         /\ o.after=o.before\o assigned /\ o.afterPending=b.pending
         /\ \A e\in SeqSet(b.entries):e.id#0 => e.id\in RequestId /\
              o.requests[e.id].kind=e.kind /\
              IF e.kind="V2" THEN o.requests[e.id].changes=e.changes /\ o.requests[e.id].transition=e.transition
              ELSE o.requests[e.id].target=e.target
       ELSE o.after=o.before
\* Pending mutation on quota drop deliberately remains unresolved.
RevisedProposalConfigurationDecisions == \A o\in audit.proposals:RevisedProposalContract(o)
RevisedOutcomeSoundness == \A o\in audit.proposals:o.decision=RevisedExpectedDecision(ProposalOutcome(o))
TransferCancellationContract(o) ==
 (o.fatal="" /\ o.role="Leader" /\ o.node\in VoterIDs(o.after) /\ o.after.voters#{}) =>
 o.afterTransfer=IF o.oldTransfer\in VoterIDs(o.after) THEN o.oldTransfer ELSE 0
TransferCancellationOnConfigurationChange == \A o\in audit.switches:TransferCancellationContract(o)
\* DRAFT ONLY. No liveness validation. Service premise must be instantiated with
\* fair communication, persistence, Ready/Advance AND ordered callbacks; no new
\* client write and no requirement to re-cross a previously acknowledged index.
AutoLeaveCompletionUnder(service) ==
 service => \A n\in Server: (raft[n].config.autoLeave /\ raft[n].config.outgoing#{}) ~>
                         (raft[n].config.outgoing={} /\ ~raft[n].config.autoLeave)
'''
for v in ['V01','V02','V03']:
 d=R/'out/revised-spec'/v;shutil.copytree(R/'versions'/v/'spec',d,dirs_exist_ok=True)
 base=(d/'base.tla').read_text()
 camp=op(base,'CampaignContract','TransferObservation').replace('CampaignContract(o)','RevisedCampaignContract(o)').replace('singleton==IsSingleton(o.config)','singleton==JointWon(o.config,{o.node})')
 # Common references to campaign contract must follow its definition.
 s='---------------- MODULE Maintenance ----------------\nEXTENDS base\n'+camp+common+(auto3 if v=='V03' else auto12)+common_end
 if v!='V01':s+=ready
 if v=='V03':s+=proposal
 s+='\n====================================================\n'
 s=s.replace('=<<','= <<').replace('#<<','# <<')
 (d/'Maintenance.tla').write_text(s)
 cfg=(R/'versions'/v/'spec/base.cfg').read_text()
 # Full preserved safety suite, explicit selected replacements; no run requested.
 cfg=cfg.replace('SPECIFICATION Spec','SPECIFICATION MaintainedSpec')
 replacements={'CampaignDecisionEligibility':'RevisedCampaignDecisionEligibility','ConfigurationTransitionSafety':'RevisedConfigurationTransitionSafety','AckPreservation':'RevisedAckPreservation','AutoLeaveAdvance':'RevisedAutoLeaveAdvance'}
 if v!='V01':replacements.update(ReadyOwnership='RevisedReadyOwnership',ReadyAccounting='RevisedReadyAccounting')
 if v=='V03':replacements.update(ProposalConfigurationDecisions='RevisedProposalConfigurationDecisions',OutcomeSoundness='RevisedOutcomeSoundness')
 for a,b in replacements.items():cfg=re.sub(r'\b'+a+r'\b',b,cfg)
 if 'RevisedAutoLeaveAdvance' not in cfg:cfg+='\nINVARIANT RevisedAutoLeaveAdvance\n'
 if v!='V01':
  for n in ['RevisedReadyOwnership','AdvancePreservesPendingOutput']:
   if n not in cfg:cfg+='\nINVARIANT '+n+'\n'
 if v=='V03':cfg+='\nINVARIANT TransferCancellationOnConfigurationChange\n'
 selected=['ElectionSafety','LogMatching','LeaderCompleteness','CommittedHistory','AppliedAgreement','TypeOK','LogStructure','VoteRecovery','RecoveryBacking','PromiseBacking','ConfigurationOrigin','RevisedConfigurationTransitionSafety','LearnerEligibility','QuorumAccounting','ReplicationEvidence','SnapshotBacking','RevisedAckPreservation','ReadyAccounting' if v=='V01' else 'RevisedReadyAccounting','QuotaIntegrity','OutcomeSoundness' if v!='V03' else 'RevisedOutcomeSoundness','ReadBasis','ReadApplication','ReadCorrelation','NoUnexpectedFatal','VoteDecisionEligibility','RevisedCampaignDecisionEligibility','TransferDecisionEligibility','RequestCorrelatedConfigurationEffects','ProposalConfigurationDecisions' if v!='V03' else 'RevisedProposalConfigurationDecisions','JointConfigurationShape','JointSnapshotRecovery','RevisedAutoLeaveAdvance']
 if v!='V01':selected+=['RevisedReadyOwnership','AdvancePreservesPendingOutput']
 if v=='V03':selected+=['TransferCancellationOnConfigurationChange']
 cfg=cfg.split('\\* Standard safety contracts')[0]+'\nINVARIANTS\n    '+'\n    '.join(selected)+'\nCHECK_DEADLOCK FALSE\n'
 (d/'selected-invariants.json').write_text(json.dumps(selected,indent=2))
 (d/'Maintenance.cfg').write_text(cfg)
 # Historical modules for actual old operator evaluation with the same constants.
 for ov in ['V00','V01','V02']:
  txt=(R/'versions'/ov/'spec/base.tla').read_text().replace('MODULE base','MODULE Historical'+ov)
  (d/f'Historical{ov}.tla').write_text(txt)
# Focused cases only, retain newly forbidden old behaviors.
cs=json.loads((R/'prior-action-evidence/V03/code-inputs.json').read_text()); byid={c['id']:c for c in cs}
ids=['vote-learner-MsgVote-grant','vote-learner-MsgVote-stale-log','vote-voter-MsgVote-grant','hup-learner',
'ready-raw-False-2-1-Leader-2','ready-node-False-2-1-Leader-2',
'advance-v02-raw-heartbeat','advance-v02-node-heartbeat','advance-v02-raw-readack','advance-v02-node-readack',
'advance-raw-True-2-0-Leader-2','advance-raw-True-2-16-Leader-2',
'v03-advance-raw-cross-0','v03-advance-raw-cross-17','v03-advance-raw-equal-old-0','v03-advance-raw-zero-cursor-0',
'v03-advance-node-cross-0','v03-advance-node-cross-17',
'v03-prop-simple-0-empty-auto','v03-prop-joint-0-v2','v03-prop-joint-0-empty-auto',
'v03-prop-joint-0-empty-explicit','v03-prop-batch-joint-add-then-leave','v03-prop-batch-simple-leave-then-add',
'v03-quota-17-empty','v03-quota-17-one-byte','v03-quota-0-large',
'v03-apply-demote-Leader','v03-apply-staged-demote-Leader','v03-apply-leave-demote-Leader',
'quorum-joint-1','quorum-joint-2','quorum-joint-0','apply-joint-demote']
missing=set(ids)-byid.keys();assert not missing,missing
cases=[byid[i] for i in ids]+json.loads((R/'coordinator-property-pilot/cases.json').read_text())
cases += [byid['apply-legacy-demote']]
(O/'cases.json').write_text(json.dumps(cases,indent=2))
for v in ['V01','V02','V03']:
 m=json.loads((R/'out/framework/targets/etcd/manifest.json').read_text());m['implementation']['command'][1]='out/validation/go-adapter/run.py';m['implementation']['command']+=['--source',f'versions/{v}/source']
 (O/f'manifest-{v}-original.json').write_text(json.dumps(m,indent=2))
 m['model']['command'][1]='out/validation/adapter/run.py'
 (O/f'manifest-{v}-observed.json').write_text(json.dumps(m,indent=2))
print('built',len(cases),'focused cases')
