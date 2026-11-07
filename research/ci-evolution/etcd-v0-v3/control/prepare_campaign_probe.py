from pathlib import Path
import shutil,json,hashlib
R=Path(__file__).resolve().parents[1];P=R/'experiments/campaign-prefix/V01';P.mkdir(parents=True,exist_ok=False)
for n in ['base.tla','Trace.tla']:shutil.copy2(R/'work/V01/spec'/n,P/n)
f=P/'base.tla';s=f.read_text();assert s.count('singleton==IsSingleton(o.config)')==1;f.write_text(s.replace('singleton==IsSingleton(o.config)','singleton==JointWon(o.config,{o.node})'))
prior=Path('/home/ubuntu/specula-etcd-ci-init-20260912.FNeLj3NS/ci-clean/runs/20260913-175006-a818/etcd-raft/.specula-output/traces/joint-autoleave.ndjson');shutil.copy2(prior,P/'trace.ndjson')
(P/'CampaignProbe.tla').write_text(r'''-------------------------- MODULE CampaignProbe --------------------------
EXTENDS Trace
VARIABLES probeDone, probeNode
probeVars == <<traceVars,probeDone,probeNode>>
ProbeTraceFile == "trace.ndjson"
ProbeInit == TraceInit /\ probeDone=FALSE /\ probeNode=0
PrefixStep == /\ ~probeDone /\ l<=Len(TraceLog) /\ TraceNext
              /\ UNCHANGED <<probeDone,probeNode>>
\* A changed entry type may affect the unchanged election consumer. Branch
\* at any observed prefix, through the original public reference Action.
\* Old RawNode callers must not mutate the core during an outstanding Ready.
CampaignBranch == /\ ~probeDone
    /\ \E n\in Server:
        /\ n\notin RawNodes \/ ~ready[n].active
        /\ Campaign(n,raft[n].timeout)
        /\ probeNode'=n
    /\ probeDone'=TRUE /\ UNCHANGED l
ProbeNext == PrefixStep \/ CampaignBranch
ProbeSpec == ProbeInit /\ [][ProbeNext]_probeVars
=============================================================================
''')
cfg=(R/'work/V01/spec/TraceCorrespondence.cfg').read_text().split('INVARIANTS')[0]
cfg=cfg.replace('SPECIFICATION TraceSpec','SPECIFICATION ProbeSpec').replace('CONSTANTS','CONSTANTS\n    JsonFile <- ProbeTraceFile',1)
cfg+='\nINVARIANT CampaignDecisionEligibility\nCHECK_DEADLOCK FALSE\n';(P/'CampaignProbe.cfg').write_text(cfg)
(P/'provenance.json').write_text(json.dumps({'trace':str(prior),'trace_sha256':hashlib.sha256(prior.read_bytes()).hexdigest(),'source_version':'V01','prefix_mode':'exact source-post validated original TraceNext from TraceInit','branch':'one original Campaign action at any prefix, with conservative old-RawNode caller ordering','property_repair':'Campaign-local singleton now JointWon(config,{self}), previously validated with four local code/model/witness controls','scope':'under-approximate guided reference-model search, not exhaustive checking'},indent=2)+'\n')
print(P)
