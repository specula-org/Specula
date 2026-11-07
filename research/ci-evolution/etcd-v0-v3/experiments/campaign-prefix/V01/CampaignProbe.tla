-------------------------- MODULE CampaignProbe --------------------------
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
