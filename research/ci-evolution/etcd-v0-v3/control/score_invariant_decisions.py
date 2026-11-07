"""Coordinator rubric scoring; semantic decisions, not executable edit validation."""
from pathlib import Path
import json,datetime
R=Path(__file__).resolve().parents[1]
out=R/'results/invariant-decisions';out.mkdir(exist_ok=True)
p=out/'judgment-score.json'
d=json.loads(p.read_text()) if p.exists() else {'scope':'Three developmental version transitions; no reliability/completeness proof. First judgment scoring is separate from candidate verification.','transitions':{}}
d['transitions']['V01']={'status':'first_decision_frozen','assessment':'All four preregistered core rubric rows addressed; concrete predicate validity still requires execution. No observed omission yet requiring independent rewrite.','core_obligations':[
 {'id':'advance_append','expected':'modify','decision':'modify','properties':['AckPreservation','AutoLeaveSerialization','AutoLeaveProgress'],'score':'detected','note':'Precisely requires retained prefix and one eligible leave entry, rejects arbitrary append or repeated outstanding leave.'},
 {'id':'joint_quorum','expected':'adapt','decision':'modify','properties':['QuorumAccounting','ConfigurationTransitionSafety'],'score':'detected','note':'Both majorities; internal id=0 leave is not constructor bootstrap exemption.'},
 {'id':'campaign_v2','expected':'preserve intent and adapt coverage','decision':'modify observer/representation','properties':['CampaignDecisionEligibility'],'score':'detected','note':'Explicitly refuses copying implementation legacy-only scan into correctness requirement.'},
 {'id':'unchanged_safety','expected':'keep','decision':'keep','properties':['ElectionSafety','LogMatching','LeaderCompleteness','CommittedHistory','AppliedAgreement','VoteRecovery'],'score':'correct_retention','note':'Implementation changes do not weaken safety.'}],
 'broad_output':{'old_properties':35,'keep':21,'modify':14,'remove':0,'additions':15,'unresolved':1},
 'unvalidated_extensions':'Additional obligations outside the existing observation/model scope are proposals, not scored successes or accepted edits.'}
d['updated_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();p.write_text(json.dumps(d,indent=2)+'\n')
print(p)
