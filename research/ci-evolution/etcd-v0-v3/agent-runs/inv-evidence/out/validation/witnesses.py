"""Serialize recorded TLA observations into executable tests. No property evaluation in Python."""
from pathlib import Path
import json,sys
R=Path('/workspace');tag=sys.argv[1] if len(sys.argv)>1 else 'final'
rows={v:{r['id']:r for r in map(json.loads,(R/f'out/validation/replay-{v}-{tag}/model.jsonl').read_text().splitlines())} for v in ['V01','V02','V03']}
setfields={'voters','outgoing','learners','learnersNext','acks','confirmAcks','voteRequests','responses','started','done','installed'}
def tla(x,key=''):
 if isinstance(x,bool):return str(x).upper()
 if isinstance(x,int):return str(x)
 if isinstance(x,str):return json.dumps(x)
 if isinstance(x,list):
  a,b=('{','}') if key in setfields else ('<<','>>');return a+', '.join(tla(i) for i in x)+b
 if isinstance(x,dict):
  if key in ['outBefore','outAfter','messages','remainingMessages'] or any(k.startswith('[') for k in x):
   if not x:return 'EmptyBag'
   return ' (+) '.join('SetToBag({'+k+'})' for k,v in x.items() for _ in range(v))
  if key=='requests':
   return '[q \\in {'+', '.join(x)+'} |-> CASE '+' [] '.join('q='+k+' -> '+tla(v) for k,v in x.items())+']'
  return '['+', '.join(k+' |-> '+tla(v,k) for k,v in x.items())+']'
 raise ValueError(x)
def obs(v,id):
 r=rows[v][id];o=r['property_truth']['observation'].copy()
 # Earlier diagnostic runs omitted decision; final run records this actual value.
 if 'quotaAfter' in o and 'cursor' in o and 'decision' not in o:o['decision']=r['model_witnesses']['coreDecision']
 return tla(o)
helpers=r'''
ConfigTruth(c) == LET M==INSTANCE Maintenance WITH history <- [EmptyHistory EXCEPT !.commitUses={c}] IN M!RevisedConfigurationTransitionSafety
ConfigOld(c) == LET M==INSTANCE base WITH history <- [EmptyHistory EXCEPT !.commitUses={c}] IN M!ConfigurationTransitionSafety
JointTruth(c) == LET M==INSTANCE base WITH history <- [EmptyHistory EXCEPT !.commitUses={c}] IN M!QuorumAccounting
FlatTruth(c) == LET M==INSTANCE HistoricalV00 WITH history <- [H0!EmptyHistory EXCEPT !.commitUses={
 [voters |-> VoterIDs(c.config),matches |-> c.matches]}] IN M!QuorumAccounting
LearnerOld(h) == LET M==INSTANCE HistoricalV01 WITH history <- h IN M!LearnerEligibility
LearnerNew(h) == LET M==INSTANCE base WITH history <- h IN M!LearnerEligibility
CheckedAck(a) == LET M==INSTANCE Maintenance WITH audit <- [EmptyAudit EXCEPT !.advances={a}] IN M!RevisedAckPreservation
CheckedReadyAccounting(a) == LET M==INSTANCE Maintenance WITH audit <- [EmptyAudit EXCEPT !.advances={a}], history <- EmptyHistory IN M!RevisedReadyAccounting
WeakPrefix(a) == Covers(a.after,a.before) /\ AdvanceEnvelope(a)
\* Real native V00 Step comparison on flat predecessor projection. Joint input
\* itself has no V00 state type or API; do not label it rejected.
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
QC == [config |-> JointR.config,matches |-> {1,2},hist |-> Hist(JointR),oldCommit |-> 1,term |-> 2]
JointEntry == V2Entry(2,Len(BootLog)+1,7,<<Change("Remove",1),Change("AddVoter",4)>>,"JointExplicit",8,16)
JointHistory == Append(BootLog,JointEntry)
LeaveHistory == Append(JointHistory,V2Entry(2,Len(JointHistory)+1,0,<<>>,"Auto",0,6))
BadLeaveCommit == [hist |-> LeaveHistory,oldCommit |-> Len(JointHistory),config |-> ConfigOf(LeaveHistory),matches |-> {2,3,4},term |-> 2]
GoodLeaveCommit == [BadLeaveCommit EXCEPT !.config=ConfigOf(JointHistory),!.matches={1,2,3,4}]
BootCommit == [hist |-> BootLog,oldCommit |-> 0,config |-> EmptyConfig,matches |-> {},term |-> 1]
'''
for v in ['V01','V02','V03']:
 d=R/'out/revised-spec'/v;defs=[];tests=[];metadata=[]
 def const(name,expr):defs.append(name+' == '+expr);return name
 def add(id,old,new,eo,en,kind,source,record='"see source"'):
  tests.append('[id |-> '+json.dumps(id)+',old |-> ('+old+'),candidate |-> ('+new+'),expectedOld |-> '+tla(eo)+',expectedCandidate |-> '+tla(en)+',kind |-> '+json.dumps(kind)+',observation |-> '+record+']')
  metadata.append(dict(id=id,kind=kind,source=source))
 add('joint-union-majority','FlatTruth(QC)','JointTruth(QC)',True,False,'semantic-witness','Native old flat union projection; full joint state unrepresentable in V00','QC')
 add('joint-both-majorities','FlatTruth([QC EXCEPT !.matches={1,2,3}])','JointTruth([QC EXCEPT !.matches={1,2,3}])',True,True,'allowed-control','Both joint voter halves acknowledge')
 add('nonvoter-contribution','FlatTruth([QC EXCEPT !.matches={1,2,3,4}])','JointTruth([QC EXCEPT !.matches={1,2,3,4}])',False,False,'mutation-negative','Deliberately fabricated nonvoter match; not an implementation bug')
 add('leave-id-zero-wrong-predecessor','ConfigOld(BadLeaveCommit)','ConfigTruth(BadLeaveCommit)',True,False,'semantic-witness','Constructed commit event from ConfigOf on explicit bootstrap/joint/leave log','BadLeaveCommit')
 add('leave-joint-predecessor','ConfigOld(GoodLeaveCommit)','ConfigTruth(GoodLeaveCommit)',True,True,'allowed-control','Predecessor is complete joint configuration','GoodLeaveCommit')
 add('actual-bootstrap-exemption','ConfigOld(BootCommit)','ConfigTruth(BootCommit)',True,True,'allowed-control','Exact BootLog positions are constructor anchors','BootCommit')
 for name in ['joint-self-quorum-False','joint-self-quorum-True','pending-v2-retained-obligation-False','pending-v2-retained-obligation-True']:
  o=const('C'+str(len(defs)),obs(v,name));pending=name.startswith('pending')
  add(name,'CampaignContract('+o+')','RevisedCampaignContract('+o+')',False,not pending,'retained-negative' if pending else 'semantic-witness',f'replay-{v}-{tag}/{name}',o)
 # Ack differential, with exact actual observation and two distinct weakenings.
 o=const('AckGood',obs(v,'v03-advance-raw-cross-0'))
 add('valid-auto-append','Ack0('+o+')','CheckedAck('+o+')',False,True,'semantic-witness',f'replay-{v}-{tag}/v03-advance-raw-cross-0',o)
 bad=const('AckBadExtra','[AckGood EXCEPT !.after=Append(@,Entry(2,Len(@)+1,"Normal",0,0,0,8))]')
 add('prefix-only-is-too-weak','WeakPrefix('+bad+')','CheckedAck('+bad+')',True,False,'mutation-negative','Append unrelated normal entry to valid actual Advance observation',bad)
 bad=const('AckBadLeave','[AckGood EXCEPT !.after[Len(AckGood.after)].transition="JointExplicit"]')
 add('empty-v2-is-not-necessarily-leave','AckFrozen('+bad+')','CheckedAck('+bad+')',True,False,'mutation-negative','Change automatic leave Transition only',bad)
 bad=const('AckWrongCursor','[AckGood EXCEPT !.applied=@+1]')
 add('captured-cursor-retained','Ack0('+bad+')','CheckedAck('+bad+')',False,False,'mutation-negative','Violate unchanged exact applied cursor obligation',bad)
 bad=const('AckWrongSnap','[AckGood EXCEPT !.oldSnap=9,!.batchSnap=3,!.afterSnap=0]')
 add('newer-snapshot-retained','AckFrozen('+bad+')','CheckedAck('+bad+')',False,False,'mutation-negative','Deliberately remove newer pending snapshot',bad)
 if v in ['V01','V02']:
  add('successful-leave-may-update-pending','AutoOld([AckGood EXCEPT !.pendingAfter=Len(AckGood.after)])','CheckedAck([AckGood EXCEPT !.pendingAfter=Len(AckGood.after)])',True,True,'allowed-control','Corrected pending cursor on real successful leave observation')
  o=const('AckOutstanding',obs(v,'auto-outstanding-leave'))
  add('outstanding-leave-not-duplicated','AckFrozen('+o+')','CheckedAck('+o+')',True,False,'semantic-witness',f'replay-{v}-{tag}/auto-outstanding-leave',o)
  o=const('AutoZero',obs(v,'v03-advance-raw-zero-cursor-0'))
  add('positive-cursor-observer','AutoOld('+o+')','RevisedAutoLeaveContract('+o+')',False,True,'observer-witness',f'replay-{v}-{tag}/v03-advance-raw-zero-cursor-0',o)
 if v!='V01':
  o=const('LearnerVote',obs(v,'vote-learner-MsgVote-grant'))
  add('learner-grant','H1!VoteContract('+o+')','VoteContract('+o+')',False,True,'semantic-witness',f'replay-{v}-{tag}/vote-learner-MsgVote-grant',o)
  o=const('LearnerStale',obs(v,'vote-learner-MsgVote-stale-log'))
  bad=const('LearnerBadGrant','[LearnerStale EXCEPT !.responses={ [x EXCEPT !.reject=FALSE]:x\\in @},!.afterVote=@]')
  add('learner-stale-log-cannot-grant','H1!VoteContract('+bad+')','VoteContract('+bad+')',False,False,'mutation-negative','Flip the actual stale-log rejection; old silence requirement also rejects',bad)
  const('LG','[EmptyHistory EXCEPT !.grants={[learner |-> TRUE]},!.campaigns={[learner |-> FALSE]}]')
  add('learner-grant-history','LearnerOld(LG)','LearnerNew(LG)',False,True,'semantic-witness','Constructed nonempty grant/campaign records; grant backed by learner-grant action','LG')
  add('learner-campaign-still-forbidden','LearnerOld([LG EXCEPT !.campaigns={[learner |-> TRUE]}])','LearnerNew([LG EXCEPT !.campaigns={[learner |-> TRUE]}])',False,False,'mutation-negative','Constructed forbidden learner campaign; not current code bug')
  o=const('ReadyAccepted',obs(v,'ready-raw-False-2-1-Leader-2'))
  add('ready-acceptance','ReadyOld('+o+')','RevisedReadyContract('+o+')',False,True,'semantic-witness',f'replay-{v}-{tag}/ready-raw-False-2-1-Leader-2',o)
  old=const('ReadyPrior',obs('V01','ready-raw-False-2-1-Leader-2'))
  add('old-ready-retention-forbidden','ReadyOld('+old+')','RevisedReadyContract('+old+')',True,False,'old-behavior-control',f'replay-V01-{tag}/ready-raw-False-2-1-Leader-2',old)
  add('ready-quota-still-owned-by-advance','ReadyOld([ReadyAccepted EXCEPT !.quotaAfter=@+1])','RevisedReadyContract([ReadyAccepted EXCEPT !.quotaAfter=@+1])',False,False,'mutation-negative','Alter quota on actual accepted Ready')
  o=const('NewReadAck',obs(v,'advance-v02-raw-readack'))
  old=const('OldReadAck',obs('V01','advance-v02-raw-readack'))
  add('advance-later-output-survives','Ack0('+old+')','PendingOutputContract('+old+')',True,False,'old-behavior-control',f'replay-V01-{tag}/advance-v02-raw-readack',old)
  add('advance-later-output-allowed','Ack0('+o+')','PendingOutputContract('+o+')',True,True,'allowed-control',f'replay-{v}-{tag}/advance-v02-raw-readack',o)
  add('false-lost-read-observer','AccountingWith(OldLost('+o+'))','CheckedReadyAccounting('+o+')',False,True,'observer-witness','Old observer applied to real new pre/post read8, captured read7',o)
  bad=const('NoOriginalReadsLost','[NewReadAck EXCEPT !.batchReads=<<>>,!.readsAfter=<<>>]')
  add('empty-batch-must-not-hide-read-loss','AccountingWith(OldLost('+bad+'))','CheckedReadyAccounting('+bad+')',True,False,'mutation-negative','Constructed loss of real later read with no original batch reads',bad)
 if v=='V03':
  old=const('AutoPrior',obs('V02','v03-advance-raw-cross-0'))
  add('old-auto-effect-not-enough','AutoOld('+old+')','RevisedAutoLeaveContract('+old+')',True,False,'old-behavior-control',f'replay-V02-{tag}/v03-advance-raw-cross-0',old)
  bad=const('AutoMissingPending','[AckGood EXCEPT !.pendingAfter=AckGood.pendingBefore]')
  add('auto-pending-barrier','AutoOld('+bad+')','RevisedAutoLeaveContract('+bad+')',True,False,'mutation-negative','Canonical nil-payload leave but omitted pending index update',bad)
  o=const('AutoNotCross',obs(v,'v03-advance-raw-equal-old-0'))
  add('noncrossing-no-leave','AutoOld('+o+')','RevisedAutoLeaveContract('+o+')',False,True,'semantic-witness',f'replay-{v}-{tag}/v03-advance-raw-equal-old-0',o)
  for id in ['v03-prop-simple-0-empty-auto','v03-prop-joint-0-v2','v03-prop-batch-joint-add-then-leave','v03-prop-batch-simple-leave-then-add','v03-quota-17-empty']:
   o=const('Prop'+str(len(defs)),obs(v,id));old=const('OldProp'+str(len(defs)),obs('V02',id))
   add(id,'ProposalContract('+o+')','RevisedProposalContract('+o+')',False,True,'semantic-witness',f'replay-{v}-{tag}/{id}',o)
   add('old-behavior-'+id,'ProposalContract('+old+')','RevisedProposalContract('+old+')',True,False,'old-behavior-control',f'replay-V02-{tag}/{id}',old)
  o=const('ExplicitEmpty',obs(v,'v03-prop-joint-0-empty-explicit'))
  add('documented-leave-classification','ProposalContract('+o+')','RevisedProposalContract('+o+')',True,False,'actual-replay-requirement-failure',f'replay-{v}-{tag}/v03-prop-joint-0-empty-explicit',o)
  o=const('Zero',obs(v,'v03-quota-17-empty'))
  add('zero-payload-outcome','Zero.decision=ExpectedDecision(ProposalOutcome(Zero))','Zero.decision=RevisedExpectedDecision(ProposalOutcome(Zero))',False,True,'semantic-witness',f'replay-{v}-{tag}/v03-quota-17-empty',o)
  o=const('Positive',obs(v,'v03-quota-17-one-byte'))
  add('positive-payload-control','Positive.decision=ExpectedDecision(ProposalOutcome(Positive))','Positive.decision=RevisedExpectedDecision(ProposalOutcome(Positive))',True,True,'allowed-control',f'replay-{v}-{tag}/v03-quota-17-one-byte',o)
  add('positive-payload-illegal-accept','"Accepted"=ExpectedDecision(ProposalOutcome(Positive))','"Accepted"=RevisedExpectedDecision(ProposalOutcome(Positive))',False,False,'mutation-negative','Force acceptance of the real positive payload rejection')
  for id,expected in [('v03-apply-demote-Leader',True),('v03-apply-staged-demote-Leader',True),('v03-apply-leave-demote-Leader',True)]:
   o=const('Switch'+str(len(defs)),obs(v,id))
   # Old observer has no callback coverage; do not turn empty quantification into truth.
   add(id,'"not-observed"','TransferCancellationContract('+o+')','not-observed',True,'new-coverage',f'replay-{v}-{tag}/{id}',o)
   bad=const('BadSwitch'+str(len(defs)),'['+o+' EXCEPT !.afterTransfer=IF @=0 THEN '+o+'.oldTransfer ELSE 0]')
   add('mutation-'+id,'"not-observed"','TransferCancellationContract('+bad+')','not-observed',False,'mutation-negative','Reverse actual cancel/preserve decision',bad)
  # Old callback observation populated from the actual V02 mapped pre/post outputs.
  r=rows['V02']['v03-apply-demote-Leader'];p=r['pre_observation'];a=r['observation']['state']
  o=const('OldSwitch',tla(dict(node=1,role=p['role'],before=p['config'],after=a['config'],oldTransfer=p['transfer'],afterTransfer=a['transfer'],fatal=r['raw_fatal'])))
  add('old-demotion-transfer-remains','"not-observed"','TransferCancellationContract('+o+')','not-observed',False,'old-behavior-control',f'replay-V02-{tag}/v03-apply-demote-Leader',o)
 s='---------------- MODULE Witnesses ----------------\nEXTENDS Checks\nVARIABLE probe\nWitnessEmptyEncoded == 6\nWitnessBootstrapPayload == 6\nWitnessBootstrapEncoded == 14\n'+helpers+'\n'+'\n'.join(defs)+'\nRows == <<\n'+',\n'.join(tests)+'\n>>\n'
 s+=r'''
WitnessInit == /\ probe=0 /\ raft=EmptyFunction /\ disk=EmptyFunction /\ ready=EmptyFunction
 /\ application=EmptyFunction /\ requests=EmptyFunction /\ wire=EmptyBag /\ history=EmptyHistory /\ quality=EmptyQuality /\ audit=EmptyAudit
WitnessNext == probe'=probe /\ FALSE
WitnessCheck ==
 /\ \A t\in SeqSet(Rows):Assert(t.old=t.expectedOld /\ t.candidate=t.expectedCandidate,"unexpected " \o t.id \o " old=" \o ToString(t.old) \o " candidate=" \o ToString(t.candidate))
 /\ Assert(FlatPost.commit=2 /\ JointPost.commit=1 /\ JointEnough.commit=2,"actual original quorum transitions")
 /\ JsonSerialize("truth-table.json",[rows |-> Rows,nativeTransitions |-> [oldFlatCommit |-> FlatPost.commit,newJointCommit |-> JointPost.commit,newJointSufficient |-> JointEnough.commit,oldFlatCommitUses |-> FlatPost.commitUses,newJointCommitUses |-> JointEnough.commitUses]])
==============================
'''
 if v=='V01':s=s.replace('IN M!RevisedReadyAccounting','IN M!ReadyAccounting')
 s=s.replace('=<<','= <<').replace('#<<','# <<')
 (d/'Witnesses.tla').write_text(s)
 cfg=(R/'out/framework/adapters/tla/constants.cfg').read_text();cfg=cfg.replace('INIT LocalInit','INIT WitnessInit').replace('NEXT LocalNext','NEXT WitnessNext').replace('INVARIANT Emit','INVARIANT WitnessCheck').replace('Joining = {1,2,3,4}','Joining = {4}').replace('EmptyEncoded <- LocalEmptyEncoded','EmptyEncoded <- WitnessEmptyEncoded').replace('BootstrapPayload <- LocalBootstrapPayload','BootstrapPayload <- WitnessBootstrapPayload').replace('BootstrapEncoded <- LocalBootstrapEncoded','BootstrapEncoded <- WitnessBootstrapEncoded')+'\n RawNodes = {1,2,3,4}\n'
 (d/'Witnesses.cfg').write_text(cfg)
 (d/'witness-index.json').write_text(json.dumps(metadata,indent=2))
 print(v,len(tests))
