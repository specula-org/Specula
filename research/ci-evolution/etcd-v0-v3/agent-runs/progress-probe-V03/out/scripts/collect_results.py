import json,pathlib,re
root=pathlib.Path('out')
primary=['ordinary-v03','ordinary-v2-v03','clocked-leadership-v03','clocked-leadership-v02','clocked-deferred-v03','clocked-deferred-v02','entering-deferred-v02','normal-cost-control-v03','explicit-control-v03','witness-completion-v03','clocked-witness-transfer-v02','witness-explicit-v03','concrete-replay-leadership-v03','concrete-replay-deferred-v03']
issues={
 'diagnostic-normal-v03':'driver syntax error',
 'diagnostic-normal-v03b':'incomplete driver successor: indentation',
 'normal-v03':'incomplete driver successor: indentation',
 'normal-v03-fixed':'incomplete monitor assignment: Boolean precedence',
 'normal-v02':'configuration referenced V03-only operators',
 'leadership-v02':'driver CHOOSE evaluated on empty publication bag',
 'focused-deferred-v03':'passed restricted scheduling, but intended missed-crossing antecedent not reached',
 'deferred-v03':'passed restricted scheduling, but intended missed-crossing antecedent not reached',
 'witness-deferred-v03':'nonvacuity check did not reach the intended antecedent; driver subsequently corrected',
 'fair-deferred-v03':'separate duplicate-leave fatal when deferring the leave application; not liveness failure',
 'fair-deferred-v02':'separate duplicate-leave fatal when deferring the leave application; not liveness failure',
 'ordinary-v03':'default MC has no V2 workload; resource/safety baseline, not a C03 liveness check',
 'ordinary-v2-v03':'ordinary MC with V2 workload added; timeout is inconclusive, not a liveness violation'
}
runs=[]
statre=re.compile(r'([\d,]+) states generated(?: \([^\n]*?\))?, ([\d,]+) distinct states found(?: \([^\n]*?\))?, ([\d,]+) states left on queue')
for p in sorted((root/'runs').glob('*/run.json')):
 r=json.load(open(p));errors=[];stats=None;depth=None;back=[]
 for line in open(p.parent/'tlc.log'):
  if line.startswith(('Progress(',*'0123456789')):
   m=statre.search(line)
   if m:stats=[int(v.replace(',','')) for v in m.groups()]
  elif line.startswith('The depth of the complete state graph search is '):depth=int(re.search(r'is (\d+)',line).group(1))
  elif line.startswith('Error:'):errors.append(line.strip())
  elif line.startswith('Back to state '):back.append(int(re.search(r'state (\d+)',line).group(1)))
 r.update(primary=r['name'] in primary,stats=dict(zip(['generated','distinct','queued'],stats)) if stats else None,counts_are_final=r['exit_code'] not in [124,137],exploration_completed=r['exit_code']==0,depth=depth,errors=errors,loop_targets=back,log=str(p.parent/'tlc.log'))
 if (p.parent/'counterexample.json').exists():r['counterexample']=str(p.parent/'counterexample.json')
 if (p.parent/'reference-actions.json').exists():r['reference_actions']=str(p.parent/'reference-actions.json')
 if r['exit_code']==124:result='timeout_inconclusive'
 elif any('Temporal properties were violated' in e for e in errors):result='liveness_violation'
 elif any('Invariant NoFatal' in e for e in errors):result='separate_safety_violation'
 elif any('Invariant No' in e for e in errors):result='nonvacuity_witness'
 elif r['exit_code']==0:result='completed_pass'
 else:result='driver_or_configuration_error'
 r['result']=result
 if r['name'] in issues:r['interpretation']=issues[r['name']]
 runs.append(r)
result={
 'candidate_id':'C03',
 'candidate_status':'rejected',
 'status_meaning':'Rejected as a progress property satisfied by the supplied V03 implementation/model. The intended automatic-exit requirement is source-supported; its counterexamples do not invalidate that requirement.',
 'requirement_assessment':'Source-supported conditional automatic exit; no universal time/step bound inferred. Formalized and tested for one reachable applied episode.',
 'v03_result':'Fair liveness violations under leadership transfer and deferred installation, replayed through original reference actions without VIEW.',
 'v02_result':'Same-domain all-voter-tick leadership control passes (nonvacuous). Deferred installation also has a fair liveness failure in V02, so that failure is not solely introduced by V03.',
 'real_implementation_bug_reproduced':False,
 'source_backed_modeling_repairs':[],
 'original_inputs_unchanged':json.load(open(root/'final-input-integrity.json')),
 'properties':{
   'episode':'request 1, entering entry j=5; incoming {1,2,4}; outgoing {1,2,3}',
   'barrier':'history of inherited Last at each leader election; eligibility uses max(j, barrier[n]); never aliases pendingConf',
   'eligible':'installed joint AutoLeave episode; voter leader; A>=max(j,b); no retained semantic exit; no retained configuration entry with index>A',
   'proposal':'forall n: (eventually always Healthy and leader-voter(n)) => (Eligible(n) leads-to RetainedExit(n))',
   'completion':'forall n: (eventually always Healthy and leader-voter(n)) => (EpisodeInstalled(n) leads-to Settled)',
   'settled':'semantic exit actually applied on incoming voters 1,2,4; outgoing empty; AutoLeave false',
   'normal_path':'Supplementary NormalCrossingEffect assertion only; never a liveness antecedent',
   'formal_artifacts':['out/drivers/C03Progress.tla','out/drivers/C03Clocked.tla','out/drivers/C03Controls.tla']
 },
 'environment':{
   'domains':'out/domains.json',
   'servers':[1,2,3,4],'bootstrap_peers':[1,2,3],'joining':[4],
   'healthy':'all nodes alive and nonfatal; storage available; no drops, duplicates, crashes, partitions, new client requests, compaction, or snapshots in suffix',
   'quorum':'all nodes reliable; majorities of both incoming and outgoing halves available',
   'ticks':'leader tick after drain, then one tick per other current voter; repeat unboundedly',
   'fairness':['WF(ClockReplay)','WF(ClockPump)','WF(FollowerTick)'],
   'network':'fixed per-node CHOOSE selection among current finite messages, reliable drain; not exploration of all permutations',
   'interactions':'optional transfer 1->2 at any reference-action boundary before first automatic proposal; optional ordered entering-entry deferral at any eligible caller position/node',
   'budgets':{'transfer':1,'deferral':1,'ticks':'unbounded','service':'unbounded'},
   'constraints':'no focused term/log/state constraint, no finite service budget',
   'view':'Only raft.readySeq, Ready.id, application job.batch canonicalized to 0; all remaining state/budgets/monitors retained; no VIEW in concrete replays'
 },
 'reachability':{
   'prefix_events':153,'prefix_transitions':152,'seed_imported':False,
   'trace_origin':'Real V02 execution only; V03 evidence is fresh MODEL execution',
   'prefix':'out/joint-autoleave-prefix-full.ndjson','replay_inputs':'out/joint-autoleave-prefix-inputs.ndjson',
   'enforcement':'Original Init plus MatchEvent for each input; PrefixApplicable rejects disabled events; no old post-state equality',
   'concretization':'Both primary lassos executed from Init with an additional loop, using original actions, no VIEW, no imported protocol state'
 },
 'counterexamples':[
  {'case':'leadership','version':'V03','run':'clocked-leadership-v03','cycle_start':466,'cycle_length':192,'final_leader':2,'term':3,'A':6,'P':5,'j':5,'barrier':5,'last':6,'exit_retained':False,'artifact':'out/runs/clocked-leadership-v03/counterexample.json'},
  {'case':'deferred installation','version':'V03','run':'clocked-deferred-v03','cycle_start':337,'cycle_length':192,'final_leader':1,'term':2,'A':5,'P':5,'j':5,'effective_barrier':5,'last':5,'exit_retained':False,'artifact':'out/runs/clocked-deferred-v03/counterexample.json'},
  {'case':'deferred installation old-version control','version':'V02','run':'clocked-deferred-v02','artifact':'out/runs/clocked-deferred-v02/counterexample.json'},
  {'case':'separate duplicate-leave fatal','versions':['V02','V03'],'runs':['fair-deferred-v02','fair-deferred-v03'],'liveness_evidence':False}
 ],
 'source_controls':json.load(open(root/'source-controls.json')),
 'coverage_limits':['No source-level reproduction of the new schedules','No exhaustive full-MC liveness result','Snapshot-restored example not separately exercised','No reachable quota-overlimit setup explored; zero-cost append checked on normal path and justified algebraically from source','Not every message ordering, multi-episode workload, partition/recovery, or unbounded leadership schedule explored'],
 'runs':runs,
 'report':'out/report.md','driver_audit':'out/driver-audit.md','public_api_reproduction_plan':'out/reproduction-plan.md'
}
json.dump(result,open(root/'results.json','w'),indent=2)
rows=[]
for name in primary:
 r=next((r for r in runs if r['name']==name),None)
 if not r:continue
 s=r['stats'];rows.append(f"| `{name}` | {r['result']} | {s['generated']:,} | {s['distinct']:,} | {r['elapsed_seconds']:.2f} s |")
(root/'run-table.md').write_text('| Run | Outcome | Generated | Distinct | Wall time |\n|---|---|---:|---:|---:|\n'+'\n'.join(rows)+'\n')
print('Collected',len(runs),'runs')
