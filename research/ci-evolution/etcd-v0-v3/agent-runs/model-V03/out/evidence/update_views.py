from pathlib import Path
p=Path('out/repaired-spec/MC.tla');s=p.read_text().replace('Original == INSTANCE base','''\\* V03 keeps all existing action bounds. MCInit includes the changed Bootstrap
\\* Progress.Next; Core/ReactiveActions inherit admission, quota, probing and
\\* auto-leave from base. Correctness predicates below are unchanged assets.
Original == INSTANCE base''');p.write_text(s)
p=Path('out/repaired-spec/Update.tla');s=p.read_text();a=s.index('Incremental view');b=s.index('Framed(a)',a)
s=s[:a]+'''Incremental view for the supplied V03 source (old source is V02).
Behavior is owned by base/MC; this view adds no transition oracle. MCInit covers
Bootstrap and empty construction. These action groups include changed methods
and unchanged producers/consumers. The retained predicates below are assets for
next-phase analysis, not revised V03 correctness claims.
***************************************************************************)

'''+s[b:]
s=s.replace('\\* V02-U1: learner vote requests now follow the ordinary vote/log-freshness\n\\* path, while learner campaigns remain rejected.', '\\* Unchanged election consumers plus V03 campaign request ordering. The message\n\\* bag abstraction intentionally omits ordering among distinct recipients.')
s=s.replace('\\* V02-U2: public RawNode.Ready and delivered Node Ready now both accept\n\\* SoftState/messages/read states; Advance preserves later output.', '\\* V03 advance: reduce quota first, cross pending from below, append nil V2,\n\\* and update pending to the appended index. Both Ready ownership paths remain.')
s=s.replace('\\* V02-U3: construction and a successful live snapshot restore reconstruct all\n\\* ConfState fields. The unchanged pre-restore membership guard remains in focus.', '\\* V03 initProgress changes live restore, but constructor Reset overwrites its\n\\* initial Next. Full ConfState and the unchanged snapshot membership guard stay.')
s=s.replace('\\* Existing configuration transitions create the joint states consumed by all\n\\* three changed mechanisms.', '\\* V03 proposal phase admission, empty payload quota, new peer probing and\n\\* transfer cancellation; legacy/V2 and normal proposals share the callers.')
s=s.replace('AffectedConfigurationActions ==\n', '''AffectedConfigurationActions ==
    \\/ \\E n\\in Server,id\\in RequestId,kind\\in WorkloadKinds\\{"Read","V2"},
          target\\in Server\\cup{0},w\\in PayloadWeights,z\\in EncodedWeights,
          parent\\in RequestId\\cup{0},ctx\\in {id,0}:
          MCInvoke(n,id,kind,target,w,z,parent,ctx)
''')
s=s.replace('AffectedActions ==', '''\\* switchToConfig probes all progress; these unchanged messages consume the
\\* resulting Next, ProbeSent, inflights and transfer target.
AffectedProgressActions ==
    \\/ \\E n,p\\in Server,t\\in Timeouts:MCTransfer(n,p,t)
    \\/ \\E m\\in DOMAIN wire,t\\in Timeouts:
         /\\ m.type\\in {"MsgApp","MsgAppResp","MsgHeartbeat","MsgHeartbeatResp", "MsgTimeoutNow"}
         /\\ Framed(Original!Receive(m,t))

AffectedActions ==''')
s=s.replace('    \\/ AffectedConfigurationActions','    \\/ AffectedConfigurationActions\n    \\/ AffectedProgressActions')
p.write_text(s)
p=Path('out/repaired-spec/Trace.tla');s=p.read_text();s=s.replace('TraceEmptyEncoded == TraceSettings.EmptyEncoded','''TraceEmptyEncoded == TraceSettings.EmptyEncoded
\\* V03 automatic leave is nil Data: the same measured encoding as an empty
\\* normal Entry. The settings schema remains compatible; no guessed payload.
TraceAutoLeaveWeight == 0
TraceAutoLeaveEncoded == TraceEmptyEncoded''')
s=s.replace('\\* Each wrapper dispatches', '''\\* V03 bindings: Init -> NewRawNode/Bootstrap; ApplyEntry -> applyConfChange,
\\* switchToConfig and Node confc; Advance -> the pending-index crossing;
\\* Restart -> newRaft restore then Reset. Old predicates are retained in configs.
\\* Each wrapper dispatches''');p.write_text(s)
for name in ['Trace.cfg','TraceCorrespondence.cfg']:
 p=Path('out/repaired-spec')/name;s=p.read_text();s=s.replace('    EmptyEncoded <- TraceEmptyEncoded','    EmptyEncoded <- TraceEmptyEncoded\n    AutoLeaveWeight <- TraceAutoLeaveWeight\n    AutoLeaveEncoded <- TraceAutoLeaveEncoded');p.write_text(s)
p=Path('out/framework/adapters/tla/LocalActions.tla');s=p.read_text().replace('{"DropQuota","DropTransfer","DropRemoved"}', '{"DropQuota","DropTransfer","DropRemoved","DropNoLeader","DropForwardDisabled"}');p.write_text(s)
