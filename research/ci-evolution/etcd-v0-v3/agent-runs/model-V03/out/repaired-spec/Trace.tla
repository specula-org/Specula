------------------------------- MODULE Trace -------------------------------
EXTENDS base, Json, IOUtils

(***************************************************************************
Category A linear NDJSON replay. One event per base action, full action calls,
no silent state changes, mandatory complete observed post-state equality.
Typed JSON values retain sets/maps/bags without lossy JSON-key conversion.
The encoding and source mapping are specified in instrumentation-spec.md.
***************************************************************************)
JsonFile == IF "JSON"\in DOMAIN IOEnv THEN IOEnv.JSON ELSE "../traces/trace.ndjson"
RawTrace == ndJsonDeserialize(JsonFile)
TraceLog == SelectSeq(RawTrace,LAMBDA e:e.tag="trace")
RECURSIVE Decode(_)
Decode(v) ==
    CASE v.tag="atom" -> v.value
      [] v.tag="seq" -> [k\in DOMAIN v.value |-> Decode(v.value[k])]
      [] v.tag="set" -> {Decode(v.value[k]):k\in DOMAIN v.value}
      [] v.tag="record" -> [k\in DOMAIN v.value |-> Decode(v.value[k])]
      [] v.tag="map" ->
         LET keys=={Decode(v.value[k].key):k\in DOMAIN v.value} IN
         IF Assert(Cardinality(keys)=Len(v.value),"Duplicate semantic trace map key") THEN
           [key\in keys |-> LET k==CHOOSE j\in DOMAIN v.value:Decode(v.value[j].key)=key
                            IN Decode(v.value[k].value)] ELSE EmptyFunction
      [] OTHER -> Assert(FALSE,"Unknown typed trace value tag")
TraceSettings == Decode(TraceLog[1].settings)
TraceBootstrapPayload == TraceSettings.BootstrapPayload
TraceBootstrapEncoded == TraceSettings.BootstrapEncoded
TraceEmptyEncoded == TraceSettings.EmptyEncoded
\* V03 automatic leave is nil Data: the same measured encoding as an empty
\* normal Entry. The settings schema remains compatible; no guessed payload.
TraceAutoLeaveWeight == 0
TraceAutoLeaveEncoded == TraceEmptyEncoded
TraceServer == TraceSettings.Server
TraceBootPeers == TraceSettings.BootPeers
TraceJoining == TraceSettings.Joining
TraceRawNodes == TraceSettings.RawNodes
TracePreVoteNodes == TraceSettings.PreVoteNodes
TraceCheckQuorumNodes == TraceSettings.CheckQuorumNodes
TraceNoForwardNodes == TraceSettings.NoForwardNodes
TraceRequestId == TraceSettings.RequestId
TracePayloadWeights == TraceSettings.PayloadWeights
TraceEncodedWeights == TraceSettings.EncodedWeights
TraceElectionTick == TraceSettings.ElectionTick
TraceHeartbeatTick == TraceSettings.HeartbeatTick
TraceMaxInflight == TraceSettings.MaxInflight
TraceMaxMsgSize == TraceSettings.MaxMsgSize
TraceMaxReadySize == TraceSettings.MaxReadySize
TraceMaxUncommitted == TraceSettings.MaxUncommitted
TraceSendPolicy == TraceSettings.SendPolicy
TracePersistPolicy == TraceSettings.PersistPolicy
TraceEarlyAdvance == TraceSettings.EarlyAdvance
TraceReadFence == TraceSettings.ReadFence
TraceCancelChanges == TraceSettings.CancelChanges
TraceCancelUnknownRemovals == TraceSettings.CancelUnknownRemovals
TraceRecoveryMode == TraceSettings.RecoveryMode

VARIABLE l
traceVars == <<vars,l>>
logline == TraceLog[l]
IsEvent(name) == l<=Len(TraceLog) /\ logline.event=name
\* Four oracle-only accumulated sets are recomputed by actions, not supplied by
\* instrumentation. All remaining source/caller fields are required observations.
ObservedRaft(r) == [k\in DOMAIN r\{"wins","grants","campaigns","commitUses"} |-> r[k]]
Observed == [raft |-> [n\in Server |-> ObservedRaft(raft[n])], disk |-> disk,
             ready |-> ready, application |-> application, requests |-> requests, wire |-> wire]
ValidatePostState(e) == Observed'=Decode(e.post)
SettingsFields == {"BootstrapPayload", "BootstrapEncoded", "EmptyEncoded", "BootPeers", "Server", "Joining", "RawNodes", "PreVoteNodes", "CheckQuorumNodes", "NoForwardNodes", "RequestId", "PayloadWeights", "EncodedWeights", "ElectionTick", "HeartbeatTick", "MaxInflight", "MaxMsgSize", "MaxReadySize", "MaxUncommitted", "SendPolicy", "PersistPolicy", "EarlyAdvance", "ReadFence", "CancelChanges", "CancelUnknownRemovals", "RecoveryMode"}
\* Post equality already fixes every initial timeout. Select that unique
\* candidate, retaining the original timeout-domain check below.
TraceInitialTimeoutAssignments ==
    {[n\in Server |-> Decode(TraceLog[1].post).raft[n].timeout]}
TraceInit == /\ DOMAIN TraceSettings=SettingsFields
             /\ \A n\in Server: Decode(TraceLog[1].post).raft[n].timeout \in ElectionTick..(2*ElectionTick-1)
             /\ DOMAIN TraceLog[1]={"tag","ts","event","settings","post"}
             /\ Len(TraceLog)>0 /\ TraceLog[1].event="Init"
             /\ Init /\ Observed=Decode(TraceLog[1].post) /\ l=2

\* V03 bindings: Init -> NewRawNode/Bootstrap; ApplyEntry -> applyConfChange,
\* switchToConfig and Node confc; Advance -> the pending-index crossing;
\* Restart -> newRaft restore then Reset. Old predicates are retained in configs.
\* Each wrapper dispatches to the full base action; params are mandatory, never
\* conditional field checks. Every wrapper is followed by ValidatePostState.
TraceTick(p) == Tick(p.node,p.timeout)
TraceCampaign(p) == Campaign(p.node,p.timeout)
TraceTickQuiesced(p) == TickQuiesced(p.node)
TraceTransferLeader(p) == TransferLeader(p.node,p.target,p.timeout)
TraceInvoke(p) == Invoke(p.node,p.id,p.kind,p.target,p.weight,p.encoded,p.parent,p.context)
TraceInvokeV2(p) == InvokeV2(p.node,p.id,p.changes,p.transition,p.weight,p.encoded,p.parent)
TracePropose(p) == Propose(p.node,p.id,p.timeout)
TraceReadIndex(p) == ReadIndex(p.node,p.id,p.timeout)
TraceReturnAPI(p) == ReturnAPI(p.id)
TraceCancel(p) == Cancel(p.id)
TraceReceive(p) == Receive(p.message,p.timeout)
TraceLose(p) == Lose(p.message)
TraceDuplicate(p) == Duplicate(p.message)
TraceReportSnapshot(p) == ReportSnapshot(p.node,p.message,p.failed,p.timeout)
TraceReportUnreachable(p) == ReportUnreachable(p.node,p.message,p.timeout)
TraceReady(p) == Ready(p.node)
TraceStartPersist(p) == StartPersist(p.node,p.part)
TraceCompletePersist(p) == CompletePersist(p.node,p.part)
TraceStorageApplySnapshot(p) == StorageApplySnapshot(p.node)
TraceStorageAppend(p) == StorageAppend(p.node)
TraceStorageSetHardState(p) == StorageSetHardState(p.node)
TracePublish(p) == Publish(p.node)
TraceQueueApplication(p) == QueueApplication(p.node)
TraceAdvance(p) == Advance(p.node)
TraceApplySnapshot(p) == ApplySnapshot(p.node)
TraceApplyEntry(p) == ApplyEntry(p.node,p.timeout)
TraceFinishApplication(p) == FinishApplication(p.node)
TraceSaveApplication(p) == SaveApplication(p.node)
TraceCompleteWrite(p) == CompleteWrite(p.node,p.id)
TraceCompleteRead(p) == CompleteRead(p.node,p.id,p.position)
TraceCreateSnapshot(p) == CreateSnapshot(p.node,p.index)
TracePersistLocalSnapshot(p) == PersistLocalSnapshot(p.node)
TraceCompact(p) == Compact(p.node,p.index)
TraceSnapshotAvailability(p) == SnapshotAvailability(p.node,p.available)
TraceCrash(p) == Crash(p.node)
TraceStop(p) == Stop(p.node)
TraceRestart(p) == Restart(p.node,p.timeout)
ExpectedParams(event) ==
    CASE event="Tick" -> {"node", "timeout"}
      [] event="Campaign" -> {"node", "timeout"}
      [] event="TickQuiesced" -> {"node"}
      [] event="TransferLeader" -> {"node", "target", "timeout"}
      [] event="Invoke" -> {"context", "encoded", "id", "kind", "node", "parent", "target", "weight"}
      [] event="InvokeV2" -> {"changes", "encoded", "id", "node", "parent", "transition", "weight"}
      [] event="Propose" -> {"id", "node", "timeout"}
      [] event="ReadIndex" -> {"id", "node", "timeout"}
      [] event="ReturnAPI" -> {"id"}
      [] event="Cancel" -> {"id"}
      [] event="Receive" -> {"message", "timeout"}
      [] event="Lose" -> {"message"}
      [] event="Duplicate" -> {"message"}
      [] event="ReportSnapshot" -> {"failed", "message", "node", "timeout"}
      [] event="ReportUnreachable" -> {"message", "node", "timeout"}
      [] event="Ready" -> {"node"}
      [] event="StartPersist" -> {"node", "part"}
      [] event="CompletePersist" -> {"node", "part"}
      [] event="StorageApplySnapshot" -> {"node"}
      [] event="StorageAppend" -> {"node"}
      [] event="StorageSetHardState" -> {"node"}
      [] event="Publish" -> {"node"}
      [] event="QueueApplication" -> {"node"}
      [] event="Advance" -> {"node"}
      [] event="ApplySnapshot" -> {"node"}
      [] event="ApplyEntry" -> {"node", "timeout"}
      [] event="FinishApplication" -> {"node"}
      [] event="SaveApplication" -> {"node"}
      [] event="CompleteWrite" -> {"id", "node"}
      [] event="CompleteRead" -> {"id", "node", "position"}
      [] event="CreateSnapshot" -> {"index", "node"}
      [] event="PersistLocalSnapshot" -> {"node"}
      [] event="Compact" -> {"index", "node"}
      [] event="SnapshotAvailability" -> {"available", "node"}
      [] event="Crash" -> {"node"}
      [] event="Stop" -> {"node"}
      [] event="Restart" -> {"node", "timeout"}
      [] OTHER -> {}
MatchEvent(e) == LET p==Decode(e.params) IN
    /\ DOMAIN e={"tag","ts","event","params","post"}
    /\ DOMAIN p=ExpectedParams(e.event)
    /\ CASE e.event="Tick" -> TraceTick(p)
          [] e.event="Campaign" -> TraceCampaign(p)
          [] e.event="TickQuiesced" -> TraceTickQuiesced(p)
          [] e.event="TransferLeader" -> TraceTransferLeader(p)
          [] e.event="Invoke" -> TraceInvoke(p)
          [] e.event="InvokeV2" -> TraceInvokeV2(p)
          [] e.event="Propose" -> TracePropose(p)
          [] e.event="ReadIndex" -> TraceReadIndex(p)
          [] e.event="ReturnAPI" -> TraceReturnAPI(p)
          [] e.event="Cancel" -> TraceCancel(p)
          [] e.event="Receive" -> TraceReceive(p)
          [] e.event="Lose" -> TraceLose(p)
          [] e.event="Duplicate" -> TraceDuplicate(p)
          [] e.event="ReportSnapshot" -> TraceReportSnapshot(p)
          [] e.event="ReportUnreachable" -> TraceReportUnreachable(p)
          [] e.event="Ready" -> TraceReady(p)
          [] e.event="StartPersist" -> TraceStartPersist(p)
          [] e.event="CompletePersist" -> TraceCompletePersist(p)
          [] e.event="StorageApplySnapshot" -> TraceStorageApplySnapshot(p)
          [] e.event="StorageAppend" -> TraceStorageAppend(p)
          [] e.event="StorageSetHardState" -> TraceStorageSetHardState(p)
          [] e.event="Publish" -> TracePublish(p)
          [] e.event="QueueApplication" -> TraceQueueApplication(p)
          [] e.event="Advance" -> TraceAdvance(p)
          [] e.event="ApplySnapshot" -> TraceApplySnapshot(p)
          [] e.event="ApplyEntry" -> TraceApplyEntry(p)
          [] e.event="FinishApplication" -> TraceFinishApplication(p)
          [] e.event="SaveApplication" -> TraceSaveApplication(p)
          [] e.event="CompleteWrite" -> TraceCompleteWrite(p)
          [] e.event="CompleteRead" -> TraceCompleteRead(p)
          [] e.event="CreateSnapshot" -> TraceCreateSnapshot(p)
          [] e.event="PersistLocalSnapshot" -> TracePersistLocalSnapshot(p)
          [] e.event="Compact" -> TraceCompact(p)
          [] e.event="SnapshotAvailability" -> TraceSnapshotAvailability(p)
          [] e.event="Crash" -> TraceCrash(p)
          [] e.event="Stop" -> TraceStop(p)
          [] e.event="Restart" -> TraceRestart(p)
          [] OTHER -> FALSE
TraceNext ==
    \/ /\ l<=Len(TraceLog) /\ MatchEvent(logline)
       /\ ValidatePostState(logline) /\ l'=l+1
    \/ /\ l>Len(TraceLog) /\ UNCHANGED traceVars
TraceSpec == TraceInit /\ [][TraceNext]_traceVars /\ WF_traceVars(TraceNext)
TraceMatched == <>(l>Len(TraceLog))
=============================================================================
