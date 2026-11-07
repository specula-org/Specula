from pathlib import Path
import json,hashlib,time,collections,difflib
R=Path('/workspace');O=R/'out';V=O/'validation';versions=['V01','V02','V03'];tag='final';tags={'V01':'final-review','V02':'final-review','V03':'final'}
def read(p):return json.loads((R/p).read_text())
def dump(p,x):(R/p).write_text(json.dumps(x,indent=2)+'\n')
# All truth values below are read from TLC, never reimplemented here.
truth=[];index={}
for v in versions:
 j=read(f'out/revised-spec/{v}/truth-table.json');idx={r['id']:r for r in read(f'out/revised-spec/{v}/witness-index.json')}
 for r in j['rows']:
  t=dict(version=v,**r,source=idx[r['id']]['source']);truth.append(t);index[(v,r['id'])]=t
 assert all(t['old']==t['expectedOld'] and t['candidate']==t['expectedCandidate'] for t in j['rows'])
dump('out/validation/truth-tables.json',truth)
replay={};obschecks=[]
for v in versions:
 p=V/f"replay-{v}-{tags[v]}";m={r['id']:r for r in map(json.loads,(p/'model.jsonl').read_text().splitlines())};g={r['id']:r for r in map(json.loads,(p/'implementation.jsonl').read_text().splitlines())};comp=json.loads((p/'comparison.json').read_text());assert comp['counts']=={'match':44},comp['counts']
 replay[v]={'model':m,'code':g,'comparison':comp}
 for id,r in m.items():
  action=r['testcase']['action'];t=r['property_truth'];audit=r['migrated_audit'];q=r['actual_quality'];checks={}
  if action in ['advance_raw','advance_node']:checks={'nonempty_original_acks':len(r['nonempty_history']['acks'])>0,'nonempty_migrated_advance':len(audit['advances'])==1,'actual_record_equal':audit['advances'][0]==t['observation']}
  elif action in ['ready_raw','ready_node']:checks={'nonempty_original_ready':len(r['nonempty_history']['readyChecks'])>0,'actual_record_equal':audit['ready'][0]==t['observation']}
  elif action=='proposal':checks={'nonempty_original_quality':len(q['proposals'])==1,'actual_record_equal':audit['proposals'][0]==t['observation']}
  elif action in ['hup','vote']:
   k='campaigns' if action=='hup' else 'votes';checks={'nonempty_original_quality':len(q[k])==1,'actual_record_equal':q[k][0]==t['observation']}
  elif id.startswith('configuration-leave-commit'):checks={'nonempty_original_commit_record':len(t['observation'])==1,'expected_candidate':t['candidate']==id.endswith('good'),'old_exemption_passes':t['old'] is True}
  if checks:assert all(checks.values()),(v,id,checks);obschecks.append(dict(version=v,id=id,checks=checks))
dump('out/validation/observer-checks.json',obschecks)
requirements={
 'quorum':['joint_quorum'], 'transition':['predecessor','joint_quorum'], 'campaign':['campaign_self','serialization'],
 'ack':['serialization','auto_leave_old'], 'vote':['learner_vote'], 'ready':['ready','advance_outputs_test'],
 'autoold':['auto_leave_old'], 'autonew':['auto_effect','auto_progress','serialization'],
 'proposal':['leave_classification','proposal_phase'], 'quota':['zero_payload_test'], 'transfer':['transfer']}
mods=[]
def mod(id,vs,names,classification,reason,witnesses,controls,req):
 mods.append(dict(id=id,versions=vs,properties=names,status='accepted',classification=classification,reason=reason,witnesses=witnesses,controls=controls,requirement_evidence=requirements[req],implementation_evidence='out/validation/differential-replays.json',limits='Local validation only; source observations do not define the requirement.'))
mod('joint-quorum',['V01'],['QuorumAccounting'],'representation_and_observer_migration','Use both voter halves. A union majority can fail one half; the native V00 flat projection is explicitly lossy.', ['joint-union-majority'],['joint-both-majorities','nonvoter-contribution'],'quorum')
mod('predecessor-bootstrap',['V01','V02','V03'],['ConfigurationTransitionSafety'],'pre_existing_property_repair','Exempt only exact BootLog entries. id=0 leave still requires its predecessor configuration.', ['leave-id-zero-wrong-predecessor','configuration-leave-commit-bad'],['leave-joint-predecessor','actual-bootstrap-exemption','configuration-leave-commit-good'],'transition')
mod('campaign-self-quorum',versions,['CampaignDecisionEligibility'],'pre_existing_property_repair','Use JointWon only in CampaignContract; global read IsSingleton is unchanged. Pending V2 obligations remain.', ['joint-self-quorum-False','joint-self-quorum-True'],['pending-v2-retained-obligation-False','pending-v2-retained-obligation-True'],'campaign')
mod('advance-append',['V01','V02','V03'],['AckPreservation'],'legitimate_relaxation_with_new_serialization_coverage','Allow only the independently justified canonical automatic leave, preserve the prior prefix/cursor/snapshot and forbid another outstanding internal leave.', ['valid-auto-append'],['prefix-only-is-too-weak','empty-v2-is-not-necessarily-leave','captured-cursor-retained','newer-snapshot-retained','outstanding-leave-not-duplicated'],'ack')
mod('learner-grants',['V02','V03'],['VoteDecisionEligibility','LearnerEligibility'],'requirement_change','Learners use ordinary exact vote/log/lease/term checks; learner campaigns remain forbidden.', ['learner-grant','learner-grant-history'],['learner-stale-log-cannot-grant','learner-campaign-still-forbidden'],'vote')
mod('ready-ownership',['V02','V03'],['ReadyOwnership','AdvancePreservesPendingOutput'],'requirement_change_and_observer_migration','Public Ready accepts outputs; Advance preserves later pending output. Record returned batch and ownership fields.', ['ready-acceptance','advance-later-output-survives'],['old-ready-retention-forbidden','ready-quota-still-owned-by-advance','advance-later-output-allowed'],'ready')
mod('read-loss-observer',['V02','V03'],['ReadyAccounting'],'observer_repair','Supply actual pre/post pending-read loss on every Advance to the unchanged original pagination/accounting predicate.', ['false-lost-read-observer'],['empty-batch-must-not-hide-read-loss'],'ready')
mod('old-auto-attempt',['V01','V02'],['AutoLeaveAdvance','AutoLeaveAttemptExactness'],'observer_repair_and_new_exactness_coverage','Include positive cursor and independently compute per-call quota admission and canonical append; stale decision markers are not evidence.', ['positive-cursor-observer'],['valid-auto-append','empty-v2-is-not-necessarily-leave'],'autoold')
mod('v03-auto-effect',['V03'],['AutoLeaveAdvance'],'requirement_change_and_observer_migration','Require crossing, exactly one zero-payload canonical leave, updated pending barrier and exact quota release. This is only a local effect property.', ['old-auto-effect-not-enough','noncrossing-no-leave'],['auto-pending-barrier','valid-auto-append'],'autonew')
mod('v03-zero-payload',['V03'],['OutcomeSoundness'],'legitimate_relaxation','Zero effective payload bypasses quota; positive payload retains the old cap and other admission branches.', ['zero-payload-outcome'],['positive-payload-control','positive-payload-illegal-accept'],'quota')
mod('v03-phase-admission',['V03'],['ProposalConfigurationDecisions'],'requirement_change_and_pre_existing_content_repair','Independent left-to-right content oracle; only accepted config entries advance pending. Preserve documented LeaveJoint classification and exact content/weights.', ['v03-prop-simple-0-empty-auto','v03-prop-joint-0-v2','v03-prop-batch-joint-add-then-leave','v03-prop-batch-simple-leave-then-add'],['documented-leave-classification','old-behavior-v03-prop-joint-0-v2','old-behavior-v03-prop-batch-joint-add-then-leave'],'proposal')
mod('v03-transfer-demotion',['V03'],['TransferCancellationOnConfigurationChange'],'new_callback_coverage_of_requirement_change','Cancel only when target leaves the voter union; preserve staged outgoing voters. Keep self-demoted/removed leader and fatal early returns outside this accepted claim.', ['old-demotion-transfer-remains','v03-apply-demote-Leader','v03-apply-leave-demote-Leader'],['v03-apply-staged-demote-Leader','mutation-v03-apply-staged-demote-Leader','mutation-v03-apply-demote-Leader'],'transfer')
rejected=[
 dict(id='old-auto-pending-preservation',status='rejected',kind='validation-draft-overconstraint-not-frozen-judgment',reason='Successful V01/V02 automatic leave must not be required to preserve the old pending index. Accept a corrected index; keep serialization controls.',evidence='out/validation/rejected-pending-overconstraint/reason.json'),
 dict(id='legacy-conf-only-campaign',status='rejected',kind='pilot_deliberate_weakening_not_frozen_judgment',reason='Accepts both forbidden pending-V2 campaign observations.',evidence='coordinator-property-pilot/out/result-02.json'),
 dict(id='prefix-only-advance',status='rejected',kind='nearby_mutant_not_frozen_judgment',reason='Accepts an unrelated suffix appended by Advance.',evidence='prefix-only-is-too-weak'),
 dict(id='any-empty-v2-leave',status='rejected',kind='overbroad_existing_predicate',reason='Empty JointExplicit is not the documented LeaveJoint value.',evidence='empty-v2-is-not-necessarily-leave'),
 dict(id='length-only-proposal-leave',status='rejected',kind='implementation_derived_alternative_not_frozen_judgment',reason='Implementation admits empty JointExplicit in joint state; preserve stricter documented API contract.',evidence='documented-leave-classification')]
unresolved=[
 dict(id='V03-U4',status='unresolved',reason='Allowed early Advance versus later configuration callback may miss the crossing trigger. No fair-service progress driver was executed.',draft='out/revised-spec/V03/Maintenance.tla:AutoLeaveCompletionUnder'),
 dict(id='V03-U9',status='unresolved',reason='Eventual automatic leave and other temporal targets are not validated by these local safety/effect checks.',draft='out/revised-spec/V03/Maintenance.tla:AutoLeaveCompletionUnder'),
 dict(id='V01-V02-auto-progress',status='unresolved',reason='Serialization failures remain visible; quota retry and eventual completion were not established.'),
 dict(id='rich-configuration-provenance',status='deferred',reason='Helper application does not supply actual committed request/context provenance for complete EffectContract validation. Preserve inherited operators; do not invent handoff or bootstrap evidence.'),
 dict(id='snapshot-dispatch-observer',status='deferred',reason='V03 snapshot-dispatch observer repair and source-only restoration extras are outside this minimal selected edit set; no acceptance of the old oracle inferred.'),
 dict(id='source-only-extras',status='deferred',reason='Preview/helper ordering, probing/progress initialization additions, encoding/copies, harness/concurrency/logger, API errors, and other noncore proposals deferred by named entry in decision-dispositions.json.'),
 dict(id='pending-on-quota-drop',status='unresolved',reason='Proposal candidate checks preserved log and exact decision, but does not settle pending mutation on quota drop.'),
 dict(id='self-demoted-leader-policy',status='unresolved',reason='Transfer cancellation claim covers leaders that remain voters; early return policy requires separate adjudication.'),
 dict(id='V00-native-Go',status='unsupported',reason='No native V00 Go binding executed. V2/joint/automatic-leave API/state unavailable; native flat TLC comparison and lifted property tests are explicit.'),
]
# Explicitly classify every frozen catalog entry without making a coverage score.
dispositions=[]
accepted={v:{n for m in mods if v in m['versions'] for n in m['properties']} for v in versions}
accepted['V01'].add('AutoLeaveSerialization')
for v in versions:
 for e in read(f'decisions/{v}-decision.json')['entries']:
  n=e['name'];status='accepted_core' if n in accepted[v] else 'retained_not_revalidated' if e.get('decision') in ['keep','retain'] else 'deferred'
  if any(x in n for x in ['Progress','Completion']) and n not in accepted[v]:status='unresolved_or_deferred_not_validated'
  dispositions.append(dict(version=v,name=n,initial_decision=e.get('decision'),validation_disposition=status,reason='See accepted modification records.' if status=='accepted_core' else 'No additional adoption/coverage claim in this focused phase; original entry and property preserved.'))
dump('out/validation/decision-dispositions.json',dispositions)
# All-version real records and adjacent-version pairs, retaining complete pre/input/post.
diff=[]
for id in replay['V03']['model']:
 rec={'id':id,'action':replay['V03']['model'][id]['testcase']['action'],'versions':{},'requirement_evidence':[]}
 act=rec['action'];reqkey='campaign' if act=='hup' else 'vote' if act=='vote' else 'ack' if act.startswith('advance') else 'ready' if act.startswith('ready') else 'proposal' if act=='proposal' else 'transfer' if act=='apply' else 'quorum'
 rec['requirement_evidence']=requirements[reqkey]
 for v in versions:
  m=replay[v]['model'][id];g=replay[v]['code'][id]
  rec['versions'][v]=dict(old_or_candidate_property_truth=m['property_truth'],model_outcome=m['observation'],code_outcome=g['observation'],model_pre=m['pre_observation'],code_pre=g['pre_observation'],input=m['input_observation'],comparison='match',record_files=dict(model=f"out/validation/replay-{v}-{tags[v]}/model.jsonl",code=f"out/validation/replay-{v}-{tags[v]}/implementation.jsonl"))
 rec['V00']=dict(model='native-flat original transition available only for quorum in native-quorum/native-results.json; otherwise not executed',code='unsupported',joint_or_v2_state='not-representable',property='lifted old contract only where explicitly identified; not a native V00 transition')
 diff.append(rec)
dump('out/validation/differential-replays.json',diff)
# Join witness records to real outcomes where there is a direct corresponding case.
caseids=set(replay['V03']['model']);aliases={'valid-auto-append':'v03-advance-raw-cross-0','outstanding-leave-not-duplicated':'auto-outstanding-leave','positive-cursor-observer':'v03-advance-raw-zero-cursor-0','learner-grant':'vote-learner-MsgVote-grant','learner-grant-history':'vote-learner-MsgVote-grant','ready-acceptance':'ready-raw-False-2-1-Leader-2','old-ready-retention-forbidden':'ready-raw-False-2-1-Leader-2','advance-later-output-survives':'advance-v02-raw-readack','advance-later-output-allowed':'advance-v02-raw-readack','false-lost-read-observer':'advance-v02-raw-readack','old-auto-effect-not-enough':'v03-advance-raw-cross-0','noncrossing-no-leave':'v03-advance-raw-equal-old-0','documented-leave-classification':'v03-prop-joint-0-empty-explicit','zero-payload-outcome':'v03-quota-17-empty','positive-payload-control':'v03-quota-17-one-byte','old-demotion-transfer-remains':'v03-apply-demote-Leader','joint-union-majority':'joint-quorum-insufficient','joint-both-majorities':'joint-quorum-sufficient','leave-id-zero-wrong-predecessor':'configuration-leave-commit-bad','leave-joint-predecessor':'configuration-leave-commit-good'}
joined=[]
for t in truth:
 id=t['id'];case=id if id in caseids else aliases.get(id)
 if id.startswith('old-behavior-'):case=id[len('old-behavior-'):]
 v=t['version'];oldv={'V01':'V00','V02':'V01','V03':'V02'}[v]
 row=dict(truth=t,old_version=oldv,new_version=v,case=case,requirement_evidence_file='out/validation/requirements.json')
 if case in caseids:
  row['new_model_outcome']=replay[v]['model'][case]['observation'];row['new_code_observation']=replay[v]['code'][case]['observation']
  if oldv!='V00':row['old_model_outcome']=replay[oldv]['model'][case]['observation'];row['old_code_observation']=replay[oldv]['code'][case]['observation']
  else:row['old_model_outcome']='not-representable for joint/V2; native-flat quorum result separately recorded';row['old_code_observation']='unsupported native binding'
 else:
  row.update(old_model_outcome='not an executed transition: constructed property control',new_model_outcome='not an executed transition: constructed property control',old_code_observation='not applicable',new_code_observation='not applicable')
 joined.append(row)
dump('out/validation/witness-evidence.json',joined)
# Source-backed behavioral repairs: none. Target instrumentation repairs are separate.
dump('out/validation/behavior-repairs.json',{'repairs':[],'reason':'All supplied behavior operators retained byte-for-byte. Existing packet fidelity repairs are inherited, not counted as this phase modifications.','adapter_changes':['private Go binding type avInput renamed to avPropertyInput','nonempty actual observer instrumentation after original successor assignment','all manifests use explicit versions/Vxx/source'],'failed_attempts':['original and observed-01: Go duplicate avInput against supplied campaign test','observed-03 and part of observed-04: audit evaluated before successor assignment; no passes credited','observed-06: missing parentheses around CASE in observer assignment; no passes credited','witness-01: generated syntax errors; witness-02: constant NEXT rejected; preserved logs','final review: removed unsupported successful V01/V02 pending preservation condition; archived rejected draft and tested corrected pending control'],'boundary':'No panic projection or ordinary-message hiding added.'})
# Exact commands are already in per-run commands/comparison files; index every one.
cmdfiles=sorted(str(p.relative_to(R)) for p in V.rglob('*commands.json'))+['out/validation/native-quorum/command.json','out/validation/final-syntax.json']
dump('out/validation/command-index.json',cmdfiles)
final_seconds=sum(c['duration_seconds'] for v in versions for c in replay[v]['comparison']['commands'])
all_replay_seconds=sum(c['duration_seconds'] for p in V.glob('replay-*/comparison.json') for c in json.loads(p.read_text())['commands'])
witness_cost=[c for c in read('out/validation/witness-03-commands.json') if c['version']=='V03']+read('out/validation/witness-final-old-auto-commands.json')
# Remove only the three temporary test bindings created by the supplied runner.
for v in versions:
 p=R/f'versions/{v}/source/action_validation_test.go'
 if str(p.relative_to(R)) not in read('input-manifest.json') and p.exists():p.unlink()
manifest=read('input-manifest.json');diffs=[p for p,h in manifest.items() if not (R/p).is_file() or hashlib.sha256((R/p).read_bytes()).hexdigest()!=h]
assert not diffs,diffs
integrity={'packet_files_checked':len(manifest),'packet_differences':diffs,'behavior_modules_unchanged':{},'generic_framework_unchanged':True,'global_read_singleton_unchanged':True}
for v in versions:
 changed=[]
 for p in (R/f'versions/{v}/spec').glob('*'):
  if p.is_file() and (R/f'out/revised-spec/{v}'/p.name).read_bytes()!=p.read_bytes():changed.append(p.name)
 assert not changed;integrity['behavior_modules_unchanged'][v]=True
 assert (R/f'out/revised-spec/{v}/base.tla').read_bytes()==(R/f'versions/{v}/spec/base.tla').read_bytes()
dump('out/validation/integrity.json',integrity)
footprint={}
for v in versions:
 p=R/f'out/revised-spec/{v}/Maintenance.tla';footprint[v]={'new_maintenance_lines':len(p.read_text().splitlines()),'selected_invariants':read(f'out/revised-spec/{v}/selected-invariants.json'),'original_behavior_edits':0}
costs={'wall_seconds_since_input_hash_capture':time.time()-read('out/validation/started.json')['epoch'],'inspection_before_hash_capture_seconds':'not measured','final_replay_engine_seconds':final_seconds,'all_recorded_replay_engine_seconds_including_failed_and_diagnostic_runs':all_replay_seconds,'successful_witness_seconds':sum(c['seconds'] for c in witness_cost),'native_quorum_seconds':read('out/validation/native-quorum/command.json')['seconds'],'syntax_seconds':sum(c['seconds'] for c in read('out/validation/final-syntax.json')),'limits':{'Go_test_timeout_seconds':90,'TLC_action_timeout_seconds':80,'TLC_witness_reproduction_timeout_seconds':180,'TLC_heap':'2 GiB','TLC_workers':1,'Go_GOMAXPROCS':2},'footprint':footprint,'validation_artifact_bytes':sum(p.stat().st_size for p in V.rglob('*') if p.is_file()),'cache_and_tmp_bytes_excluded':True}
result={'phase':'validation of frozen proposed edits only','scope':'Local state/action and property-record validation; no global campaign, liveness validation, completeness or independent-generation score.','accepted':mods,'rejected':rejected,'unresolved_and_deferred':unresolved,'validation':{'replay_cases_per_version':44,'matched_code_model_pairs':132,'replay_counts':{v:replay[v]['comparison']['counts'] for v in versions},'final_replay_tags':tags,'tlc_truth_pairs':len(truth),'truth_pair_kinds':dict(collections.Counter(t['kind'] for t in truth)),'observer_record_checks':len(obschecks),'syntax_modules_checked':15,'generic_comparator_tests_passed':8,'pilot_reused':'coordinator-property-pilot/out/result-02.json','native_V00_TLC':'out/validation/native-quorum/native-results.json','native_V00_Go':'unsupported','selected_invariant_configurations':{v:f'out/revised-spec/{v}/Maintenance.cfg' for v in versions},'behavior_repairs':[],'liveness':'not validated; U4/U9 remain unresolved'},'evidence':{'truth_tables':'out/validation/truth-tables.json','witnesses_with_replays':'out/validation/witness-evidence.json','all_version_replays':'out/validation/differential-replays.json','requirement_evidence':'out/validation/requirements.json','observer_migrations':'out/validation/observer-migrations.json','observer_checks':'out/validation/observer-checks.json','state_domain_mapping':'out/validation/domain-and-mapping.md','frozen_decision_dispositions':'out/validation/decision-dispositions.json','commands':'out/validation/command-index.json','reproduce':'out/validation/README.md','triage':'out/validation/behavior-repairs.json'},'integrity':integrity,'costs':costs}
dump('out/results.json',result)
print(json.dumps({'accepted_groups':len(mods),'replays':132,'tlc_pairs':len(truth),'observer_checks':len(obschecks),'final_engine_seconds':round(final_seconds,3),'integrity_files':len(manifest)},indent=2))
